import HookQuietCounters.Queries
import ArmCert.HookQuiet.V0.TransportE20
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.CycleOff.pmu_cycle_off"
  (← IO.getStderr).flush

theorem pmu_cycle_off (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true)
    (he : s.regs.PSTATE.EL = 0#2) (hn : s.regs.PSTATE.nRW = 0#1)
    (hscr : _get_SCR_EL3_Type_RW (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1)
    (hhcr : _get_HCR_EL2_Type_RW (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1)
    (hp : _get_BRBFCR_EL1_Type_PAUSED (s.regs.bank_BitVec_64 .BRBFCR_EL1) = 1#1)
    (hE : _get_PMCR_EL0_Type_E (s.regs.bank_BitVec_64 .PMCR_EL0) = 0#1)
    (hH : _get_MDCR_EL2_Type_HPME (s.regs.bank_BitVec_64 .MDCR_EL2) = 0#1) :
    (AArch64_PMUCycle () : SailM Unit) s = .ok () (el0QueryState s) := by
  simp [AArch64_PMUCycle, bind_app, pure_apply, map_apply, read_pmcr, read_mdcr,
    hE, hH, should_brbe_paused s ha he hn hscr hhcr hp]

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CycleOff.pmu_cycle_off_quiet"
  (← IO.getStderr).flush

theorem pmu_cycle_off_quiet (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s)
    (hE : _get_PMCR_EL0_Type_E (s.regs.bank_BitVec_64 .PMCR_EL0) = 0#1)
    (hH : _get_MDCR_EL2_Type_HPME (s.regs.bank_BitVec_64 .MDCR_EL2) = 0#1) :
    ∃ t, (AArch64_PMUCycle () : SailM Unit) s = .ok () t ∧
      E20Frame s.regs t.regs ∧
      t.regs.bank_Option_InterruptID .__GIC_Pending = s.regs.bank_Option_InterruptID .__GIC_Pending ∧
      t.mem = s.mem ∧ t.events = s.events ∧
      ArmCert.HookQuiet.V0.HookQuiet budget t := by
  refine ⟨el0QueryState s,
    pmu_cycle_off s q.a64 q.el0 q.nrw q.scrRW q.hcrRW q.brbePaused hE hH,
    rfl, rfl, rfl, rfl, ?_⟩
  exact ArmCert.HookQuiet.V0.hookQuiet_of_regs_eq (s := s) (t := el0QueryState s) rfl q

#print axioms pmu_cycle_off
#print axioms pmu_cycle_off_quiet

end HookQuietCounters
