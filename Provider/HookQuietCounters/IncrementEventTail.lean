import HookQuietCounters.IncrementEventMiddle
import Lean.Elab.Command
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.PMUWriteFrame
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
namespace HookQuietCounters

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.IncrementEventTail.increment_event_mark"
  (← IO.getStderr).flush

theorem increment_event_mark (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat) :
    ∃ t, IncrementEventParts.mark idx s = .ok () t ∧ PMUPost budget s t := by
  let v1 := BitVec.update (PMOVSSET_EL0.get s.regs) idx (Bit 1#1)
  let a : NativeState := {s with regs := PMOVSSET_EL0.set v1 s.regs}
  have fa := (write_PMOVSSET_EL0 budget s q v1).2.1
  let v2 := BitVec.update (PMOVSCLR_EL0.get a.regs) idx (Bit 1#1)
  let t : NativeState := {a with regs := PMOVSCLR_EL0.set v2 a.regs}
  have ft := (write_PMOVSCLR_EL0 budget a fa.quiet v2).2.1
  refine ⟨t, ?_, fa.trans ft⟩
  simp only [IncrementEventParts.mark, bind_app, read_apply, write_apply]
  rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.IncrementEventTail.increment_event_chain"
  (← IO.getStderr).flush

theorem increment_event_chain (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat) (lp : BitVec 1) :
    ∃ t, IncrementEventParts.chain idx lp s = .ok () t ∧ PMUPost budget s t := by
  by_cases hpar : BitVec.join1 [integer_access (idx : Int) 0] = 0#1
  · by_cases hn : (idx : Int) + 1 < s.regs.bank_Int .NUM_PMU_COUNTERS
    · by_cases hp : ((! featureValue s .FEAT_PMUv3p5) || (lp == 0#1)) = true
      · obtain ⟨acc, ha⟩ := pmu_event2_acc PMU_EVENT_CHAIN 1 ((idx : Int) + 1) s q.a64 q.nrw (by omega) (by have := q.pmuCountUpper; omega)
        let t : NativeState := {s with regs := {s.regs with PMUEventAccumulator := acc}}
        have ft : PMUPost budget s t := (write_PMUEventAccumulator budget s q acc).2.1
        refine ⟨t, ?_, ft⟩
        simpa [IncrementEventParts.chain, bind_assoc, bind_if, pure_bind, bind_app, if_apply, map_apply, hpar, get_num_counters, hn, HavePMUv3p5, feature_apply, pure_apply, hp] using ha
      · refine ⟨s, ?_, PMUPost.refl budget s q⟩
        simp [IncrementEventParts.chain, bind_assoc, bind_if, pure_bind, bind_app, if_apply, map_apply, hpar, get_num_counters, hn, HavePMUv3p5, feature_apply, pure_apply, hp]
    · refine ⟨s, ?_, PMUPost.refl budget s q⟩
      simp [IncrementEventParts.chain, bind_assoc, bind_if, pure_bind, bind_app, if_apply, map_apply, hpar, get_num_counters, hn, pure_apply]
  · refine ⟨s, ?_, PMUPost.refl budget s q⟩
    simp [IncrementEventParts.chain, bind_assoc, bind_if, pure_bind, bind_app, if_apply, map_apply, hpar, pure_apply]

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.IncrementEventTail.increment_event_tail"
  (← IO.getStderr).flush

theorem increment_event_tail (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat)
    (oldValue newValue : Int) (lp : BitVec 1) (width : Int) :
    ∃ t, IncrementEventParts.tail idx oldValue newValue lp width s = .ok () t ∧ PMUPost budget s t := by
  rw [IncrementEventParts.tail_equation]
  simp only [IncrementEventParts.tailCombined]
  split
  · obtain ⟨a, ha, fa⟩ := increment_event_mark budget s q idx
    obtain ⟨t, ht, ft⟩ := increment_event_chain budget a fa.quiet idx lp
    exact ⟨t, by simp only [bind_app, ha, ht], fa.trans ft⟩
  · exact ⟨s, rfl, PMUPost.refl budget s q⟩

#print axioms increment_event_mark
#print axioms increment_event_chain
#print axioms increment_event_tail
end HookQuietCounters
