import HookQuietCounters.ICNTRBody
import HookQuietCounters.PMUWriteFrame
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.ICNTRRun.PMUPost.refl"
  (← IO.getStderr).flush

theorem PMUPost.refl (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) : PMUPost budget s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, q⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.ICNTRRun.PMUPost.trans"
  (← IO.getStderr).flush

theorem PMUPost.trans {budget : Nat} {s t u : NativeState}
    (a : PMUPost budget s t) (b : PMUPost budget t u) : PMUPost budget s u :=
  ⟨b.frame.trans a.frame, b.gic.trans a.gic, b.mem.trans a.mem, b.events.trans a.events,
    b.choiceState.trans a.choiceState, b.tags.trans a.tags, b.cycleCount.trans a.cycleCount,
    b.sailOutput.trans a.sailOutput, b.quiet⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.ICNTRRun.icntr_body_total"
  (← IO.getStderr).flush

theorem icntr_body_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (inc : Int) :
    ∃ t, ICNTRParts.body inc s = .ok () t ∧ PMUPost budget s t := by
  let old_value : Int := (s.regs.bank_BitVec_64 .PMICNTR_EL0).toNat
  let new_value : Int := old_value + inc
  let value := Mk_PMICNTR_EL0_Type (integer_subrange new_value 63 0)
  let s1 : NativeState := {s with regs := PMICNTR_EL0.set value s.regs}
  have f1 := (write_PMICNTR_EL0 budget s q value).2.1
  let ovset := Sail.BitVec.updateSubrange (s1.regs.bank_BitVec_64 .PMOVSSET_EL0) 32 32 1#1
  let s2 : NativeState := {s1 with regs := PMOVSSET_EL0.set ovset s1.regs}
  have f2 := (write_PMOVSSET_EL0 budget s1 f1.quiet ovset).2.1
  let ovclr := Sail.BitVec.updateSubrange (s2.regs.bank_BitVec_64 .PMOVSCLR_EL0) 32 32 1#1
  let s3 : NativeState := {s2 with regs := PMOVSCLR_EL0.set ovclr s2.regs}
  have f3 := (write_PMOVSCLR_EL0 budget s2 f2.quiet ovclr).2.1
  simp only [ICNTRParts.body, bind_app, read_apply, write_apply]
  split
  · refine ⟨s3, ?_, (f1.trans f2).trans f3⟩
    simp only [bind_app, read_apply, write_apply]
    rfl
  · exact ⟨s1, rfl, f1⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.ICNTRRun.instruction_counter_total"
  (← IO.getStderr).flush

theorem instruction_counter_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (inc : Int)
    (hi : featureValue s .FEAT_PMUv3_ICNTR = true) :
    ∃ t, (IncrementInstructionCounter inc : SailM Unit) s = .ok () t ∧ PMUPost budget s t := by
  have hv : CountIndexValid INSTRUCTION_COUNTER_ID s := Or.inr (Or.inr ⟨rfl, hi⟩)
  obtain ⟨counted, t, ht, hf⟩ := count_pmu_events_query budget s q INSTRUCTION_COUNTER_ID hv
  have fp := PMUPost.of_eraseOcc_eq q hf
  rw [ICNTRParts.equation]
  cases counted with
  | false => exact ⟨t, by simp only [bind_app, ht, Bool.false_eq_true, reduceIte, pure_apply], fp⟩
  | true =>
    obtain ⟨u, hu, fu⟩ := icntr_body_total budget t fp.quiet inc
    exact ⟨u, by simp only [bind_app, ht, reduceIte, hu], fp.trans fu⟩
#print axioms icntr_body_total
#print axioms instruction_counter_total
end HookQuietCounters
