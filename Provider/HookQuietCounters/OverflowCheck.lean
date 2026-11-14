import HookQuietCounters.OverflowRun
import Lean.Elab.Command
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
namespace HookQuietCounters

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.OverflowCheck.PMUPost.of_eraseOcc_eq"
  (← IO.getStderr).flush

theorem PMUPost.of_eraseOcc_eq {budget : Nat} {s t : NativeState}
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (h : eraseOcc t = eraseOcc s) :
    PMUPost budget s t := by
  have hr := eraseOcc_regs h
  have f := TimerFrame.of_eraseOcc_eq h
  refine ⟨?_, f.gic, f.mem, f.events, f.choiceState, f.tags, f.cycleCount, f.sailOutput, ?_⟩
  · change eraseE20 t.regs = eraseE20 s.regs
    rw [hr]
  · exact ArmCert.HookQuiet.V0.hookQuiet_of_regs_eq hr.symm q

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.OverflowCheck.pmu_check_overflow_total"
  (← IO.getStderr).flush

theorem pmu_check_overflow_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ∃ t, (CheckForPMUOverflow () : SailM Unit) s = .ok () t ∧ PMUPost budget s t := by
  obtain ⟨t, ht, hf⟩ := overflow_condition_masked budget s q true false true true false false
  have hr := eraseOcc_regs hf
  have qt := ArmCert.HookQuiet.V0.hookQuiet_of_regs_eq hr.symm q
  have hB := should_brbe_paused t qt.a64 qt.el0 qt.nrw qt.scrRW qt.hcrRW qt.brbePaused
  have hE : eraseOcc (el0QueryState t) = eraseOcc t := rfl
  refine ⟨el0QueryState t, ?_, PMUPost.of_eraseOcc_eq q (hE.trans hf)⟩
  cases hP : featureValue t .FEAT_PMUv3p9 <;>
    cases hD : featureValue t .FEAT_Debugv8p9 <;>
    simp [CheckForPMUOverflow, bind_assoc, bind_if, pure_bind, bind_app, ht,
      irq_low, HavePMUv3p9, Havev8p9Debug, feature_apply, hP, hD, hB, pure_apply, map_apply]
#print axioms PMUPost.of_eraseOcc_eq
#print axioms pmu_check_overflow_total
end HookQuietCounters
