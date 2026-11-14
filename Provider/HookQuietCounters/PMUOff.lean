import Bridge.CruxCore
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUOff.pure_apply"
  (← IO.getStderr).flush

theorem pure_apply {α : Type} (a : α) (s : NativeState) :
    (pure a : SailM α) s = .ok a s := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUOff.map_apply"
  (← IO.getStderr).flush

theorem map_apply {α β : Type} (f : α → β) (x : SailM α) (s : NativeState) :
    (f <$> x) s = match x s with
      | .ok a t => .ok (f a) t
      | .error e t => .error e t := by
  change EStateM.map f x s = _
  unfold EStateM.map
  cases x s <;> rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUOff.read_spe"
  (← IO.getStderr).flush

theorem read_spe (s : NativeState) :
    (readReg SPESampleInFlight : SailM Bool) s =
      .ok (s.regs.bank_Bool .SPESampleInFlight) s := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUOff.read_pmcr"
  (← IO.getStderr).flush

theorem read_pmcr (s : NativeState) :
    (readReg PMCR_EL0 : SailM (BitVec 64)) s =
      .ok (s.regs.bank_BitVec_64 .PMCR_EL0) s := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUOff.read_mdcr"
  (← IO.getStderr).flush

theorem read_mdcr (s : NativeState) :
    (readReg MDCR_EL2 : SailM (BitVec 64)) s =
      .ok (s.regs.bank_BitVec_64 .MDCR_EL2) s := rfl

/- A semantic subcase of the proposed guard, proved over the real hook.
This is not the full HookQuiet predicate or its enabled-PMU contract. -/
run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUOff.pmu_event_off"
  (← IO.getStderr).flush

theorem pmu_event_off (e : BitVec 16) (s : NativeState)
    (hSpe : s.regs.bank_Bool .SPESampleInFlight = false)
    (hE : _get_PMCR_EL0_Type_E (s.regs.bank_BitVec_64 .PMCR_EL0) = 0#1)
    (hH : _get_MDCR_EL2_Type_HPME (s.regs.bank_BitVec_64 .MDCR_EL2) = 0#1) :
    (PMUEvent e : SailM Unit) s = .ok () s := by
  simp [PMUEvent, PMUEvent__1, bind_app, pure_apply, map_apply, read_spe, read_pmcr,
    read_mdcr, hSpe, hE, hH]

#print axioms pmu_event_off

end HookQuietCounters
