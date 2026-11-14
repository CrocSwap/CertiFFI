import HookQuietCounters.CycleOff
import HookQuietCounters.Security
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUEventNonRetired.get_num_counters"
  (← IO.getStderr).flush

theorem get_num_counters (s : NativeState) :
    (GetNumEventCounters () : SailM Int) s = .ok (s.regs.bank_Int .NUM_PMU_COUNTERS) s := rfl

/- Full enabled/disabled PMU paths for events that do not increment ICNTR. -/
run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUEventNonRetired.pmu_event_nonretired_acc"
  (← IO.getStderr).flush

theorem pmu_event_nonretired_acc (e : BitVec 16) (inc : Int) (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true) (hn : s.regs.PSTATE.nRW = 0#1)
    (hs : s.regs.bank_Bool .SPESampleInFlight = false)
    (hu : s.regs.bank_Int .NUM_PMU_COUNTERS ≤ 31)
    (he : e ≠ PMU_EVENT_INST_RETIRED) :
    ∃ acc, (PMUEvent__1 e inc : SailM Unit) s =
      .ok () {s with regs := {s.regs with PMUEventAccumulator := acc}} := by
  obtain ⟨acc, hacc⟩ := event_loop_acc e inc (s.regs.bank_Int .NUM_PMU_COUNTERS) s ha hn hu
  simp [eventLoop] at hacc
  let t := {s with regs := {s.regs with PMUEventAccumulator := acc}}
  have hat (a : Vector Int 31) : (HaveAArch64 () : SailM Bool)
      {s with regs := {s.regs with PMUEventAccumulator := a}} =
      .ok true {s with regs := {s.regs with PMUEventAccumulator := a}} := have_a64 _ ha
  have hit (a : Vector Int 31) : (HavePMUv3ICNTR () : SailM Bool)
      {s with regs := {s.regs with PMUEventAccumulator := a}} =
      .ok (featureValue s .FEAT_PMUv3_ICNTR) {s with regs := {s.regs with PMUEventAccumulator := a}} := rfl
  rcases bit_cases (_get_PMCR_EL0_Type_E (s.regs.bank_BitVec_64 .PMCR_EL0)) with hE | hE <;>
    rcases bit_cases (_get_MDCR_EL2_Type_HPME (s.regs.bank_BitVec_64 .MDCR_EL2)) with hH | hH <;>
    by_cases hN : s.regs.bank_Int .NUM_PMU_COUNTERS = 0 <;>
    cases hI : featureValue s .FEAT_PMUv3_ICNTR <;>
    simp [PMUEvent__1, bind_app, pure_apply, map_apply, read_spe, hs,
      read_pmcr, read_mdcr, hE, hH, get_num_counters, hN, hacc, hat, hit,
      HavePMUv3ICNTR, have_a64, ha, feature_apply, hI, he] <;>
    first | exact ⟨s.regs.PMUEventAccumulator, rfl⟩ | exact ⟨acc, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUEventNonRetired.PMUPost"
  (← IO.getStderr).flush

structure PMUPost (budget : Nat) (s t : NativeState) : Prop where
  frame : E20Frame s.regs t.regs
  gic : t.regs.bank_Option_InterruptID .__GIC_Pending = s.regs.bank_Option_InterruptID .__GIC_Pending
  mem : t.mem = s.mem
  events : t.events = s.events
  choiceState : t.choiceState = s.choiceState
  tags : t.tags = s.tags
  cycleCount : t.cycleCount = s.cycleCount
  sailOutput : t.sailOutput = s.sailOutput
  quiet : ArmCert.HookQuiet.V0.HookQuiet budget t

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUEventNonRetired.pmu_event_nonretired_total"
  (← IO.getStderr).flush

theorem pmu_event_nonretired_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (e : BitVec 16)
    (he : e ≠ PMU_EVENT_INST_RETIRED) :
    ∃ t, (PMUEvent e : SailM Unit) s = .ok () t ∧ PMUPost budget s t := by
  obtain ⟨acc, hacc⟩ := pmu_event_nonretired_acc e 1 s q.a64 q.nrw q.spe q.pmuCountUpper he
  let t := {s with regs := {s.regs with PMUEventAccumulator := acc}}
  have hf : E20Frame s.regs t.regs := rfl
  refine ⟨t, hacc, hf, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact ArmCert.HookQuiet.V0.hookQuiet_of_E20Frame hf q

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUEventNonRetired.pmu_spec_total"
  (← IO.getStderr).flush

theorem pmu_spec_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ∃ t, (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) s = .ok () t ∧ PMUPost budget s t := by
  exact pmu_event_nonretired_total budget s q PMU_EVENT_INST_SPEC (by decide)
#print axioms get_num_counters
#print axioms pmu_event_nonretired_acc
#print axioms pmu_event_nonretired_total
#print axioms pmu_spec_total
end HookQuietCounters
