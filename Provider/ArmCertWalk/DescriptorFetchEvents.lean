import ArmCertTranslateModel.SwapEvents
import Pilot.S2FetchFrame

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

def descriptorReadEvent (acc : AccessDescriptor) (addr : AddressDescriptor) (ti : TranslationInfo) : Event :=
  let request := read_request acc (some ti) 8 addr.vaddress addr.paddress.address
  .memRead addr.paddress.address.toNat 8 (request.va.map (fun va => va.toNat)) request.access_kind request.tag

def DescriptorFetchEventEffect (acc : AccessDescriptor) (addr : AddressDescriptor) (ti : TranslationInfo) (before : State) :
    EStateM.Result (Sail.Error exception) State (FaultRecord × BitVec 64) → Prop
  | .ok _ after => after.events = before.events.push (descriptorReadEvent acc addr ti)
  | .error _ _ => False

theorem descriptor_fetch_event_effect (ee : BitVec 1) (fault : FaultRecord) (data : BitVec 64)
    (acc : AccessDescriptor) (addr : AddressDescriptor) (ti : TranslationInfo) (state : State)
    (noRME : state.regs.FeatureImpl[232] = false)
    (ram : S2TableRAM.OrdinaryRAM addr.paddress.address)
    (present : S2ByteMemory.DescAt state.mem addr.paddress.address.toNat data) :
    DescriptorFetchEventEffect acc addr ti state (FetchDescriptor ee addr acc fault 64 ti state) := by
  rw [S2FetchFrame.from_descriptor ee fault data acc addr ti state noRME ram present]
  delta S2Fetch.native
  run_tac Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
    let target ← goal.getType
    let target ← Lean.Meta.transform target (pre := fun expr => do
      if expr.isAppOf ``Nat.div.go || expr.isAppOf ``Sail.Int.toNatChecked then
        return .done (← Lean.Meta.withTransparency .all <| Lean.Meta.whnf expr)
      return .continue)
    return [← goal.change target]
  simp [DescriptorFetchEventEffect, descriptorReadEvent]

theorem descriptor_fetch_total (ee : BitVec 1) (fault : FaultRecord) (data : BitVec 64)
    (acc : AccessDescriptor) (addr : AddressDescriptor) (ti : TranslationInfo) (state : State)
    (noRME : state.regs.FeatureImpl[232] = false)
    (ram : S2TableRAM.OrdinaryRAM addr.paddress.address)
    (present : S2ByteMemory.DescAt state.mem addr.paddress.address.toNat data) :
    ∃ other, FetchDescriptor ee addr acc fault 64 ti state =
      .ok (fault, S2FetchFrame.decoded ee data) other ∧ other.regs = state.regs ∧
      other.mem = state.mem ∧ other.events = state.events.push (descriptorReadEvent acc addr ti) := by
  obtain ⟨other, call, registers, memory⟩ :=
    S2FetchFrame.total ee fault data acc addr ti state noRME ram present
  have events := descriptor_fetch_event_effect ee fault data acc addr ti state noRME ram present
  rw [call] at events
  exact ⟨other, call, registers, memory, events⟩

#print axioms descriptor_fetch_total
end ArmCertWalk
