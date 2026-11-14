import NativeEntry.Effects
import Bridge.CruxGenGuarded.BookkeepingTransport
import Bridge.CruxGenGuarded.OwnerCounterSpec
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryAdapters.PreludeInput
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded NativeEntry
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

/- Once-generic bridge for ONE actual spec-PMU successor. The fixed constructed
native-owner rule is applied internally. No public HookLaws, success, future Q,
or frame answer is supplied. The incoming control relation/pins/Q are internal
outputs of the actual fetch proof; its payload memory is never replaced by the
initial memory. Fetch/walk construction and whole-step composition remain open. -/
theorem after_spec (source fetched : NativeState)
    (input : Effects.ControlInput source fetched) (hp : StepPins fetched)
    (ticks : Nat) (hq : HookQuiet ticks fetched) :
    ∃ sp, (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      Effects.ControlInput source sp ∧ StepPins sp ∧ HookQuiet ticks sp ∧
      sp.mem = fetched.mem ∧ sp.events = fetched.events := by
  obtain ⟨sp, success, post⟩ := ArmBridge.CruxGenGuarded.Owner.spec_rule ticks fetched hq
  have controls : Effects.ControlInput fetched sp :=
    ⟨ArmBridge.CruxNonProj.npe_of_E20 post.frame, (PMUFrame.of_E20 post.frame).btn⟩
  exact ⟨sp, success, input.trans controls,
    e20_pins fetched sp hp post.frame, post.quiet, post.mem, post.events⟩

#print axioms after_spec
end NativeEntryAdapters.PreludeInput
