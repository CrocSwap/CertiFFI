import Bridge.CruxGenGuarded.EpilogueTaken
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! GENERATED internal counter composition from usingA32 spine.
All facts concern the actual counter successor and must be filled by the
fixed owner law. No global counter frame or register transformer is used. -/

def nativeAtPmuCycle : NativeState → EStateM.Result (Sail.Error exception) NativeState Unit :=
fun afterFetch =>
  ArmBridge.CruxCore.bind_app.match_1
    (fun x =>
      EStateM.Result (Sail.Error ArmFull.exception)
        (Sail.ConcurrencyInterfaceV1.SequentialState ArmFull.Regs Sail.ConcurrencyInterfaceV1.oracleChoiceSource) Unit)
    (ArmFull.Functions.AArch64_PMUCycle Unit.unit afterFetch) (fun a s' => ArmFull.Functions.__EndCycle Unit.unit s')
    fun e s' => EStateM.Result.error e s'

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.counter_boundary"
  (← IO.getStderr).flush

theorem counter_boundary (real : Type) [Sail.SailReal real] (s afterCounter : NativeState)
      (hCnt : (__UpdateSystemCounter () : SailM Unit) s = .ok () afterCounter)
      (hf4 : afterCounter.regs.FeatureImpl[4]! = true)
      (hnrw : afterCounter.regs.PSTATE.nRW = 0#1)
       :
    nativeAtCounter s = nativeAtPmuCycle afterCounter := by
  unfold ArmBridge.CruxGenGuarded.nativeAtCounter
  erw [hCnt]
  simp only [↓bind_app]
  rw [ArmBridge.BKmin.usingA32 real]
  rotate_left
  · exact hf4
  · exact hnrw
  simp only [ArmBridge.BKv.usingA32_native]
  simp only [Bool.cond_false, ↓bind_app]
  unfold nativeAtPmuCycle
  rfl

#print axioms counter_boundary
end ArmBridge.CruxGenGuarded
