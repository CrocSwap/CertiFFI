import HookQuietCounters.PMUValuePrepare
import HookQuietCounters.ICNTRRun
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUValueRun.pmu_value_commit_total"
  (← IO.getStderr).flush

theorem pmu_value_commit_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (n : Nat) (Vb : Int)
    (result : Option (Int × Bool)) :
    ∃ v t, PMUValueParts.commit n Vb result s = .ok v t ∧ PMUPost budget s t := by
  cases result with
  | none => exact ⟨Vb, s, rfl, PMUPost.refl budget s q⟩
  | some p =>
    let value := vectorUpdate s.regs.PMULastThresholdValue n p.2
    let t : NativeState := {s with regs := PMULastThresholdValue.set value s.regs}
    have fp := (write_PMULastThresholdValue budget s q value).2.1
    refine ⟨p.1, t, ?_, fp⟩
    simp only [PMUValueParts.commit, bind_app, read_apply, write_apply, pure_apply]
    rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUValueRun.pmu_count_value_total"
  (← IO.getStderr).flush

theorem pmu_count_value_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (n : Nat) (Vb : Int) (hn : n < 31) :
    ∃ v t, (PMUCountValue n Vb : SailM Int) s = .ok v t ∧ PMUPost budget s t := by
  obtain ⟨result, t, hp, hf⟩ := pmu_value_prepare_query n Vb hn s
  have fp := PMUPost.of_eraseOcc_eq q hf
  obtain ⟨v, u, hc, fc⟩ := pmu_value_commit_total budget t fp.quiet n Vb result
  refine ⟨v, u, ?_, fp.trans fc⟩
  rw [PMUValueParts.equation]
  simp only [bind_app, hp, hc]
#print axioms pmu_value_commit_total
#print axioms pmu_count_value_total
end HookQuietCounters
