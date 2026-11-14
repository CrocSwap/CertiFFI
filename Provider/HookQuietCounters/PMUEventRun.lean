import HookQuietCounters.PMUEventParts
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUEventRun.pmu_counter_stage_total"
  (← IO.getStderr).flush

theorem pmu_counter_stage_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (e : BitVec 16) (inc : Int) :
    ∃ t, PMUEventParts.counter e inc s = .ok () t ∧ PMUPost budget s t := by
  obtain ⟨acc, hacc⟩ := event_loop_acc e inc (s.regs.bank_Int .NUM_PMU_COUNTERS) s q.a64 q.nrw q.pmuCountUpper
  simp [eventLoop] at hacc
  let t : NativeState := {s with regs := {s.regs with PMUEventAccumulator := acc}}
  have fp : PMUPost budget s t := (write_PMUEventAccumulator budget s q acc).2.1
  by_cases hn : s.regs.bank_Int .NUM_PMU_COUNTERS = 0
  · exact ⟨s, by simp [PMUEventParts.counter, bind_app, get_num_counters, hn, pure_apply], PMUPost.refl budget s q⟩
  · refine ⟨t, ?_, fp⟩
    simp [PMUEventParts.counter, bind_app, get_num_counters, hn, hacc, pure_apply, unit_bind, map_apply]
    all_goals rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUEventRun.pmu_instruction_stage_total"
  (← IO.getStderr).flush

theorem pmu_instruction_stage_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (e : BitVec 16) (inc : Int) :
    ∃ t, PMUEventParts.instruction e inc s = .ok () t ∧ PMUPost budget s t := by
  have hA := have_a64 s q.a64
  cases hi : featureValue s .FEAT_PMUv3_ICNTR with
  | false =>
    exact ⟨s, by simp [PMUEventParts.instruction, bind_app, hA, HavePMUv3ICNTR, feature_apply, hi, pure_apply, map_apply], PMUPost.refl budget s q⟩
  | true =>
    by_cases he : e = PMU_EVENT_INST_RETIRED
    · obtain ⟨t, ht, ft⟩ := instruction_counter_total budget s q inc hi
      exact ⟨t, by simp [PMUEventParts.instruction, bind_app, hA, HavePMUv3ICNTR, feature_apply, hi, he, ht, pure_apply, map_apply], ft⟩
    · exact ⟨s, by simp [PMUEventParts.instruction, bind_app, hA, HavePMUv3ICNTR, feature_apply, hi, he, pure_apply, map_apply], PMUPost.refl budget s q⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUEventRun.pmu_event1_total"
  (← IO.getStderr).flush

theorem pmu_event1_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (e : BitVec 16) (inc : Int) :
    ∃ t, (PMUEvent__1 e inc : SailM Unit) s = .ok () t ∧ PMUPost budget s t := by
  obtain ⟨t, hc, fc⟩ := pmu_counter_stage_total budget s q e inc
  obtain ⟨u, hi, fi⟩ := pmu_instruction_stage_total budget t fc.quiet e inc
  rw [PMUEventParts.equation]
  rcases bit_cases (_get_PMCR_EL0_Type_E (s.regs.bank_BitVec_64 .PMCR_EL0)) with hE | hE
  · rcases bit_cases (_get_MDCR_EL2_Type_HPME (s.regs.bank_BitVec_64 .MDCR_EL2)) with hH | hH
    · refine ⟨s, ?_, PMUPost.refl budget s q⟩
      simp [PMUEventParts.combined, bind_app, read_spe, q.spe, read_pmcr, read_mdcr, hE, hH, pure_apply, map_apply]
    · refine ⟨u, ?_, fc.trans fi⟩
      simp [PMUEventParts.combined, bind_app, read_spe, q.spe, read_pmcr, read_mdcr, hE, hH, hc, hi, pure_apply, map_apply]
  · refine ⟨u, ?_, fc.trans fi⟩
    simp [PMUEventParts.combined, bind_app, read_spe, q.spe, read_pmcr, read_mdcr, hE, hc, hi, pure_apply, map_apply]

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUEventRun.pmu_event_total"
  (← IO.getStderr).flush

theorem pmu_event_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (e : BitVec 16) :
    ∃ t, (PMUEvent e : SailM Unit) s = .ok () t ∧ PMUPost budget s t :=
  pmu_event1_total budget s q e 1

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUEventRun.pmu_retired_total"
  (← IO.getStderr).flush

theorem pmu_retired_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ∃ t, (PMUEvent PMU_EVENT_INST_RETIRED : SailM Unit) s = .ok () t ∧ PMUPost budget s t :=
  pmu_event_total budget s q PMU_EVENT_INST_RETIRED
#print axioms pmu_counter_stage_total
#print axioms pmu_instruction_stage_total
#print axioms pmu_event1_total
#print axioms pmu_event_total
#print axioms pmu_retired_total
end HookQuietCounters
