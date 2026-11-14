import HookQuietCounters.CycleCounterParts
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.CycleCounterRun.elapsed64_total"
  (← IO.getStderr).flush

theorem elapsed64_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ∃ elapsed t, (HasElapsed64Cycles () : SailM Bool) s = .ok elapsed t ∧ PMUPost budget s t := by
  by_cases h : s.regs.bank_Int .__clock_divider = 63
  · let t : NativeState := {s with regs := __clock_divider.set 0 s.regs}
    exact ⟨true, t, by simp [HasElapsed64Cycles, bind_app, map_apply, if_apply, read_apply, h, write_apply, pure_apply]; rfl,
      (write___clock_divider budget s q 0).2.1⟩
  · let value := __clock_divider.get s.regs + 1
    let t : NativeState := {s with regs := __clock_divider.set value s.regs}
    exact ⟨false, t, by simp [HasElapsed64Cycles, bind_app, map_apply, if_apply, read_apply, h, write_apply, pure_apply]; rfl,
      (write___clock_divider budget s q value).2.1⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CycleCounterRun.cycle_counter_eligible_total"
  (← IO.getStderr).flush

theorem cycle_counter_eligible_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ∃ active t, CycleCounterParts.eligible s = .ok active t ∧ PMUPost budget s t := by
  obtain ⟨active, a, ha, hf⟩ := count_pmu_events_query budget s q CYCLE_COUNTER_ID (Or.inl rfl)
  have fa := PMUPost.of_eraseOcc_eq q hf
  obtain ⟨elapsed, t, he, fe⟩ := elapsed64_total budget a fa.quiet
  cases active with
  | false => exact ⟨false, a, by simp [CycleCounterParts.eligible, bind_assoc, pure_bind, bind_app, ha, pure_apply], fa⟩
  | true =>
    by_cases hLC : _get_PMCR_EL0_Type_LC (a.regs.bank_BitVec_64 .PMCR_EL0) = 1#1
    · exact ⟨true, a, by simp [CycleCounterParts.eligible, bind_assoc, pure_bind, bind_app, if_apply, ha, HaveAArch32, read_apply, hLC, pure_apply, map_apply], fa⟩
    · by_cases hD : _get_PMCR_EL0_Type_D (a.regs.bank_BitVec_64 .PMCR_EL0) = 0#1
      · exact ⟨true, a, by simp [CycleCounterParts.eligible, bind_assoc, pure_bind, bind_app, if_apply, ha, HaveAArch32, read_apply, hLC, hD, pure_apply, map_apply], fa⟩
      · exact ⟨elapsed, t, by simp [CycleCounterParts.eligible, bind_assoc, pure_bind, bind_app, if_apply, ha, HaveAArch32, read_apply, hLC, hD, he, pure_apply, map_apply], fa.trans fe⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CycleCounterRun.cycle_counter_body_total"
  (← IO.getStderr).flush

theorem cycle_counter_body_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ∃ t, CycleCounterParts.body s = .ok () t ∧ PMUPost budget s t := by
  let old : Int := BitVec.toNat (PMCCNTR_EL0.get s.regs)
  let new : Int := old + 1
  let value := Mk_PMCCNTR_EL0_Type (integer_subrange new 63 0)
  let a : NativeState := {s with regs := PMCCNTR_EL0.set value s.regs}
  have fa := (write_PMCCNTR_EL0 budget s q value).2.1
  let v1 := Sail.BitVec.updateSubrange (PMOVSSET_EL0.get a.regs) 31 31 1#1
  let w : NativeState := {a with regs := PMOVSSET_EL0.set v1 a.regs}
  have fw := (write_PMOVSSET_EL0 budget a fa.quiet v1).2.1
  let v2 := Sail.BitVec.updateSubrange (PMOVSCLR_EL0.get w.regs) 31 31 1#1
  let t : NativeState := {w with regs := PMOVSCLR_EL0.set v2 w.regs}
  have ft := (write_PMOVSCLR_EL0 budget w fw.quiet v2).2.1
  by_cases hLC : (_get_PMCR_EL0_Type_LC (PMCR_EL0.get a.regs) == 1#1) = true
  all_goals simp only [a, value, new, old] at hLC
  all_goals simp only [CycleCounterParts.body, bind_app, read_apply, write_apply, HaveAArch32,
    Bool.false_eq_true, reduceIte, pure_apply, hLC]
  all_goals try simp only [if_apply]
  all_goals
    split
    · simp only [bind_app, read_apply, write_apply, pure_apply]
      exact ⟨t, rfl, (fa.trans fw).trans ft⟩
    · exact ⟨a, rfl, fa⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CycleCounterRun.increment_cycle_counter_total"
  (← IO.getStderr).flush

theorem increment_cycle_counter_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ∃ t, (AArch64_IncrementCycleCounter () : SailM Unit) s = .ok () t ∧ PMUPost budget s t := by
  obtain ⟨active, a, ha, fa⟩ := cycle_counter_eligible_total budget s q
  obtain ⟨t, ht, ft⟩ := cycle_counter_body_total budget a fa.quiet
  rw [CycleCounterParts.equation]
  cases active with
  | false => exact ⟨a, by simp only [bind_app, ha, Bool.false_eq_true, reduceIte, pure_apply], fa⟩
  | true => exact ⟨t, by simp only [bind_app, ha, reduceIte, ht], fa.trans ft⟩
#print axioms elapsed64_total
#print axioms cycle_counter_eligible_total
#print axioms cycle_counter_body_total
#print axioms increment_cycle_counter_total
end HookQuietCounters
