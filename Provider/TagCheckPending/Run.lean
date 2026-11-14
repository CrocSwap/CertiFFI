import TagCheckFrames.ReadNoTag
import Bridge.CruxCore
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Draft ArmBridge.CruxCore
open TagCheckFrames
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace TagCheckPending
/-- The actual pending-interrupt call preserves the oracle source and tag-read
counter on success; no profile, interrupt-mask or request-value pin is needed. -/
theorem pending_preserves (request : InterruptReq) : Preserves (TakePendingInterrupts request) := by
  oracle_frame

theorem pending_source (request : InterruptReq) (s : NativeState) :
    (resCS s (TakePendingInterrupts request s)).1 = s.choiceState.1 := by
  cases run : TakePendingInterrupts request s with
  | error error t => rfl
  | ok value t => exact (pending_preserves request s value t run).1

theorem pending_counter (request : InterruptReq) (s : NativeState) :
    (resCO s (TakePendingInterrupts request s)).getD 1354 0 = s.choiceOcc.getD 1354 0 := by
  cases run : TakePendingInterrupts request s with
  | error error t => rfl
  | ok value t => simpa only [resCO, Nat.add_zero] using (pending_preserves request s value t run).2

#print axioms pending_preserves
#print axioms pending_source
#print axioms pending_counter
end TagCheckPending
