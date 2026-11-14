import NativeTagCheck.Tail
import TagCheckPending.Run
import Bridge.CruxGenGuarded.EntryPrefetch
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option Elab.async false
set_option backward.dsimp.instances true
attribute [local implicit_reducible] oracleChoiceSource
namespace NativeTagCheck
open NativeMteTagCheck

def pendingInput (s : NativeState) : NativeState :=
  {s with regs := {s.regs with bank_Int := s.regs.bank_Int.set .SEE (-1)}}

def pendingRequest (s : NativeState) : InterruptReq :=
  { take_SE := true, take_vSE := true, take_IRQ := true, take_vIRQ := true,
    take_FIQ := true, take_vFIQ := true,
    iesb_req := oracleChoiceSource.chooseAt .bool ((ChoiceLabel.site 7640).child 6) s.choiceState }

/-- Internal adapter for the actual pending-interrupt producer receipt. -/
theorem before_fetch_choice_of_pending (s : NativeState)
    (receipt : ∀ request,
      (resCS (pendingInput s) (TakePendingInterrupts request (pendingInput s))).1 = s.choiceState.1 ∧
      (resCO (pendingInput s) (TakePendingInterrupts request (pendingInput s))).getD 1354 0 =
        s.choiceOcc.getD 1354 0) : ChoiceDelta s (beforeFetchState s) 0 := by
  have selected := receipt (pendingRequest s)
  simpa only [ChoiceDelta, beforeFetchState, pendingInput, pendingRequest, Nat.add_zero] using selected

theorem before_fetch_choice (s : NativeState) : ChoiceDelta s (beforeFetchState s) 0 := by
  apply before_fetch_choice_of_pending
  intro request
  exact ⟨TagCheckPending.pending_source request (pendingInput s),
    TagCheckPending.pending_counter request (pendingInput s)⟩

#print axioms before_fetch_choice_of_pending
#print axioms before_fetch_choice
end NativeTagCheck
