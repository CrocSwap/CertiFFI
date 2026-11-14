import ArmCertTranslateModel.StoreHistorySource
import ArmCertCTNative.UpdateTrafficV2

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

def swapReadEvent (acc : AccessDescriptor) (addr : AddressDescriptor) : Event :=
  .memRead addr.paddress.address.toNat 8 (some addr.vaddress.toNat)
    (AccessDescriptor_to_Access_kind acc) false

def swapWriteEvent (ee : BitVec 1) (next : BitVec 64)
    (acc : AccessDescriptor) (addr : AddressDescriptor) : Event :=
  .memWrite addr.paddress.address.toNat 8 (some addr.vaddress.toNat)
    (AccessDescriptor_to_Access_kind acc) (some (S2Endian.encode ee next)) none

/-- Keep the raw write value and tag, alongside actual read/write order.
    This is ONE actual source swap, not a bound on writes in a walk. -/
def SwapEventEffect (ee : BitVec 1) (word : BitVec 64) (acc : AccessDescriptor)
    (addr : AddressDescriptor) (before : State) :
    EStateM.Result (Sail.Error exception) State (FaultRecord × BitVec 64) → Prop
  | .ok _ after => after.events = (before.events.push (swapReadEvent acc addr)).push
      (swapWriteEvent ee word acc addr)
  | .error _ _ => False

theorem swap_event_effect (ee : BitVec 1) (fault : FaultRecord) (prev next : BitVec 64)
    (acc : AccessDescriptor) (addr : AddressDescriptor) (ti : TranslationInfo) (state : State)
    (noRME : state.regs.FeatureImpl[232] = false)
    (ram : S2TableRAM.OrdinaryRAM addr.paddress.address)
    (present : S2ByteMemory.DescAt state.mem addr.paddress.address.toNat (S2Endian.encode ee prev)) :
    SwapEventEffect ee next acc addr state
      (AArch64_MemSwapTableDesc fault prev next ee acc addr ti state) := by
  rw [S2SwapAnyFrame.from_descriptor ee fault prev next acc addr ti state noRME ram present]
  delta S2SwapAny.native
  unfold Sail.BitVec.length
  run_tac Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
    let target ← goal.getType
    let target ← Lean.Meta.transform target (pre := fun expr => do
      if expr.isAppOf ``Nat.div.go || expr.isAppOf ``Sail.Int.toNatChecked then
        return .done (← Lean.Meta.withTransparency .all <| Lean.Meta.whnf expr)
      return .continue)
    return [← goal.change target]
  simp only [Sail.BitVec.castWidth_eq]
  dsimp
  rw [S2Bytes.join64 (S2Endian.encode ee prev)]
  by_cases endian : ee = 1#1 <;>
    simp [SwapEventEffect, swapReadEvent, swapWriteEvent, S2Endian.encode, endian,
      S2Endian.reverse_involutive] <;> rfl

/-- Strengthen the existing actual-state adapter with its exact raw events.
    No expected event history is supplied by the caller. -/
theorem swap_store_step_events (params : S1TTWParams) (footprint : Footprint)
    (operation : TableUpdate) (fault : FaultRecord) (acc : AccessDescriptor)
    (addr : AddressDescriptor) (ti : TranslationInfo) (state : State)
    (noRME : state.regs.FeatureImpl[232] = false)
    (ram : S2TableRAM.OrdinaryRAM addr.paddress.address)
    (slot : operation.slot = addr.paddress.address.toNat)
    (covered : operation.slot ∈ footprint.slots) (aligned : operation.slot % 8 = 0)
    (present : S1ByteMemory.DescAt state.mem operation.slot
      (S2Endian.encode params.ee operation.before))
    (allowed : AllowedUpdate params operation.role operation.before operation.after) :
    ∃ next,
      AArch64_MemSwapTableDesc fault operation.before operation.after params.ee acc addr ti state =
        .ok (fault, operation.after) next ∧
      next.regs = state.regs ∧ StoreStep params footprint operation state.mem next.mem ∧
      next.events = (state.events.push (swapReadEvent acc addr)).push
        (swapWriteEvent params.ee operation.after acc addr) := by
  obtain ⟨next, call, registers, stored⟩ :=
    swap_store_step params footprint operation fault acc addr ti state noRME ram slot covered aligned present allowed
  have bytes : S2ByteMemory.DescAt state.mem addr.paddress.address.toNat
      (S2Endian.encode params.ee operation.before) := by
    intro i hi; simpa only [slot] using present i hi
  have events := swap_event_effect params.ee fault operation.before operation.after acc addr ti state noRME ram bytes
  rw [call] at events
  exact ⟨next, call, registers, stored, events⟩

theorem swap_ttw_traffic (ee : BitVec 1) (word : BitVec 64)
    (acc : AccessDescriptor) (addr : AddressDescriptor)
    (kind : AccessDescriptor_to_Access_kind acc = .AK_ttw ()) :
    ArmCertCT.Native.V2.trafficOf #[swapReadEvent acc addr, swapWriteEvent ee word acc addr] =
      [⟨addr.paddress.address.toNat, 8, .ttwRead⟩,
       ⟨addr.paddress.address.toNat, 8, .ttwWrite⟩] := by
  simp [ArmCertCT.Native.V2.trafficOf, ArmCertCT.Native.V2.trafficRec,
    swapReadEvent, swapWriteEvent, kind]

#print axioms swap_event_effect
#print axioms swap_store_step_events
#print axioms swap_ttw_traffic
end ArmCert.Translate.Model
