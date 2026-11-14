import Bridge.CruxGenGuarded.Metadata
import Bridge.CruxGenGuarded.OwnerCounterSpec
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace ArmBridge.CruxGenGuarded
open ArmBridge.Draft ArmBridge.CruxCore
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

run_cmd do
  IO.eprintln "CURRENT_DECL ArmBridge.CruxGenGuarded.MetadataGuard.after_spec"
  (← IO.getStderr).flush

theorem MetadataGuard.after_spec (fetched : NativeState) (g : MetadataGuard fetched)
    (ticks : Nat) (q : HookQuiet ticks fetched) :
    ∃ sp, (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      MetadataGuard sp ∧ HookQuiet ticks sp ∧ sp.mem = fetched.mem ∧ sp.events = fetched.events := by
  obtain ⟨sp, hook, post⟩ := ArmBridge.CruxGenGuarded.Owner.spec_rule ticks fetched q
  exact ⟨sp, hook, g.after_E20 post.frame, post.quiet, post.mem, post.events⟩

#print axioms MetadataGuard.after_spec
end ArmBridge.CruxGenGuarded
