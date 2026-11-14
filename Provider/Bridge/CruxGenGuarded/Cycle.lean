import Bridge.CruxGenGuarded.Counter
import Bridge.CruxGenGuarded.QuietTransport
import Bridge.CruxGen
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! GENERATED from actual final cycle-PMU/endCycle spine. The
primitive success is INTERNAL, filled by the fixed Q-domain owner proof. -/

def nativeEndState : NativeState → NativeState :=
fun afterCycle =>
  {
    regs :=
      ArmFull.Register.__cycle_count.set (HAdd.hAdd (afterCycle.regs.bank_Int ArmFull.Bank_Int.__cycle_count) 1)
        afterCycle.regs,
    choiceState := afterCycle.choiceState, choiceOcc := afterCycle.choiceOcc, mem := afterCycle.mem,
    tags := afterCycle.tags, cycleCount := afterCycle.cycleCount, sailOutput := afterCycle.sailOutput,
    events := afterCycle.events }

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.cycle_boundary"
  (← IO.getStderr).flush

theorem cycle_boundary (real : Type) [Sail.SailReal real] (s afterCycle : NativeState)
      (hPCy : (AArch64_PMUCycle () : SailM Unit) s = .ok () afterCycle)
       :
    nativeAtPmuCycle s = .ok () (nativeEndState afterCycle) := by
  unfold ArmBridge.CruxGenGuarded.nativeAtPmuCycle
  erw [hPCy]
  simp only [↓bind_app, ArmBridge.BKmin.endCycle, ArmBridge.BKv.endCycle_native]
  try dsimp only [EStateM.bind.match_1, tc_apply.match_1, bind_app.match_1]
  rfl

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.nativeEndState_fields"
  (← IO.getStderr).flush

theorem nativeEndState_fields (s : NativeState) : GuardFieldsEq s (nativeEndState s) := by
  constructor
  all_goals first
    | rfl
    | (intro k hk; rfl)
    | (simp (disch := decide) only [nativeEndState, Register.__cycle_count, Regs.ref_Int, RegMap.set_ne])

theorem nativeEndState_quiet (ticks : Nat) (s : NativeState) (hq : HookQuiet ticks s) :
    HookQuiet ticks (nativeEndState s) :=
  quiet_of_fields ticks s _ hq (nativeEndState_fields s)

theorem nativeEndState_mem (s : NativeState) : (nativeEndState s).mem = s.mem := rfl
theorem nativeEndState_events (s : NativeState) : (nativeEndState s).events = s.events := rfl
theorem nativeEndState_pc (s : NativeState) : (nativeEndState s).regs._PC = s.regs._PC := rfl
theorem nativeEndState_cong (s : NativeState) :
    ArmBridge.CruxGen.CongOut (nativeEndState s) s := by constructor <;> rfl

#print axioms cycle_boundary
#print axioms nativeEndState_fields
#print axioms nativeEndState_quiet
#print axioms nativeEndState_mem
#print axioms nativeEndState_events
#print axioms nativeEndState_pc
#print axioms nativeEndState_cong
end ArmBridge.CruxGenGuarded
