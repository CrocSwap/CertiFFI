import HookQuietCounters.PMUCycleLoop
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUCycleRun.pmu_cycle_enabled_total"
  (← IO.getStderr).flush

theorem pmu_cycle_enabled_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ∃ t, PMUCycleParts.enabled s = .ok () t ∧ PMUPost budget s t := by
  obtain ⟨a, ha, fa⟩ := pmu_event_total budget s q PMU_EVENT_CPU_CYCLES
  obtain ⟨w, hw, fw⟩ := pmu_cycle_regular_total budget a fa.quiet (a.regs.bank_Int .NUM_PMU_COUNTERS) rfl
  obtain ⟨u, hu, fu⟩ := increment_cycle_counter_total budget w fw.quiet
  obtain ⟨t, ht, ft⟩ := pmu_check_overflow_total budget u fu.quiet
  exact ⟨t, by simp only [PMUCycleParts.enabled, bind_app, ha, get_num_counters, hw, hu, ht], ((fa.trans fw).trans fu).trans ft⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUCycleRun.pmu_cycle_total"
  (← IO.getStderr).flush

theorem pmu_cycle_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ∃ t, (AArch64_PMUCycle () : SailM Unit) s = .ok () t ∧ PMUPost budget s t := by
  obtain ⟨t, ht, ft⟩ := pmu_cycle_enabled_total budget s q
  by_cases hE : _get_PMCR_EL0_Type_E (s.regs.bank_BitVec_64 .PMCR_EL0) = 0#1
  · by_cases hH : _get_MDCR_EL2_Type_HPME (s.regs.bank_BitVec_64 .MDCR_EL2) = 0#1
    · exact ⟨el0QueryState s, pmu_cycle_off s q.a64 q.el0 q.nrw q.scrRW q.hcrRW q.brbePaused hE hH,
        PMUPost.of_eraseOcc_eq q rfl⟩
    · rw [PMUCycleParts.equation]
      cases hP : featureValue s .FEAT_PMUv3 with
      | false => exact ⟨s, by simp [PMUCycleParts.combined, bind_app, read_pmcr, read_mdcr, hE, hH, HavePMUv3, feature_apply, hP, pure_apply, map_apply], PMUPost.refl budget s q⟩
      | true => exact ⟨t, by simp [PMUCycleParts.combined, bind_app, read_pmcr, read_mdcr, hE, hH, HavePMUv3, feature_apply, hP, pure_apply, map_apply, ht], ft⟩
  · rw [PMUCycleParts.equation]
    cases hP : featureValue s .FEAT_PMUv3 with
    | false => exact ⟨s, by simp [PMUCycleParts.combined, bind_app, read_pmcr, hE, HavePMUv3, feature_apply, hP, pure_apply, map_apply], PMUPost.refl budget s q⟩
    | true => exact ⟨t, by simp [PMUCycleParts.combined, bind_app, read_pmcr, hE, HavePMUv3, feature_apply, hP, pure_apply, map_apply, ht], ft⟩
#print axioms pmu_cycle_enabled_total
#print axioms pmu_cycle_total
end HookQuietCounters
