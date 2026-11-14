-- Vendored from loops ws/LoopNative/SubImm64/Prefix.lean, renamed LoopNative.SubImm64 -> Route7Sub (route 7 unit 3,).
import Bridge.CruxGenGuarded.OwnerMetadata
import Bridge.CruxGenGuarded.Action
import NativeEntryInput.Input
import Route7Sub.Contract
import Route7Sub.Adapter
import Route7Sub.Dispatch
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace Route7Sub.TailCore
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler false
set_option profiler.threshold 1000

/- Internal fixed-class action-prefix composition over canonical states.
No initial/current memory identity or caller future action/guard is supplied.
Fetch/input/guard construction, actual tail/modelStep and landing remain open.
BTI alone permits arbitrary incoming BTYPE/BTN; the other class pin requirements
are explicit internal preconditions to derive from the actual protected phase. -/

theorem action_prefix (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (imm12 : BitVec 12) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (profile : Route7Sub.Adapter.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    ∃ sp fin,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntryInput.Input source (actionState (Route7Sub.Dispatch.selected Rd Rn imm12) sp 20) ∧
      (actionState (Route7Sub.Dispatch.selected Rd Rn imm12) sp 20).mem = fetched.mem ∧
      (actionState (Route7Sub.Dispatch.selected Rd Rn imm12) sp 20).events = fetched.events ∧
      nativeTail real source (Route7Sub.Dispatch.selected Rd Rn imm12) enc0 fetched =
        nativeAfterAction real source (Route7Sub.Dispatch.selected Rd Rn imm12) enc0 fin ∧
      Route7Sub.projection fin =
        Route7Sub.expected (actionState (Route7Sub.Dispatch.selected Rd Rn imm12) sp 20) Rd Rn imm12 ∧
      NativeEntryContract.Frame Route7Sub.Adapter.writes
        (actionState (Route7Sub.Dispatch.selected Rd Rn imm12) sp 20) fin ∧
      HookQuiet ticks fin ∧ fin.mem = fetched.mem ∧
      fin.events = fetched.events := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (Route7Sub.Dispatch.selected Rd Rn imm12) 20
  have metadataQuiet := actionState_quiet (Route7Sub.Dispatch.selected Rd Rn imm12) sp 20 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : Route7Sub.Guard (actionState (Route7Sub.Dispatch.selected Rd Rn imm12) sp 20) Rd Rn imm12 := by
    exact Route7Sub.Adapter.guard_at_metadata source sp Rd Rn imm12 (Route7Sub.Dispatch.selected Rd Rn imm12) 20 profile currentInput.controls currentPins ticks post.quiet rd rn
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    Route7Sub.Contract.run (actionState (Route7Sub.Dispatch.selected Rd Rn imm12) sp 20) Rd Rn imm12 classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (Route7Sub.Dispatch.selected Rd Rn imm12)
      (decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 0#1 1#1 1#1) 20 := by
    intro pc t see
    exact Route7Sub.Dispatch.dispatch_at real pc Rd Rn imm12 t (by simpa using see)
  have boundary := metadata_boundary_at real source (Route7Sub.Dispatch.selected Rd Rn imm12)
    (decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 0#1 1#1 1#1) enc0 sp currentGuard 20 (by decide) dispatch
  have memory : fin.mem = (actionState (Route7Sub.Dispatch.selected Rd Rn imm12) sp 20).mem := by
    exact congrArg (fun value => value.2.1) projection
  have events : fin.events = (actionState (Route7Sub.Dispatch.selected Rd Rn imm12) sp 20).events := by
    exact congrArg (fun value => value.2.2) projection
  have eventFrame : fin.events = fetched.events := by
    simpa only [actionState_events, post.events] using events
  refine ⟨sp, fin, hook, metadataInput,
    (actionState_mem (Route7Sub.Dispatch.selected Rd Rn imm12) sp 20).trans post.mem,
    (actionState_events (Route7Sub.Dispatch.selected Rd Rn imm12) sp 20).trans post.events,
    ?_, projection, frame, finalQuiet,
    memory.trans ((actionState_mem (Route7Sub.Dispatch.selected Rd Rn imm12) sp 20).trans post.mem), eventFrame⟩
  calc
    nativeTail real source (Route7Sub.Dispatch.selected Rd Rn imm12) enc0 fetched =
        afterSpecPmu real source (Route7Sub.Dispatch.selected Rd Rn imm12) enc0 sp :=
      spec_pmu_boundary real source (Route7Sub.Dispatch.selected Rd Rn imm12) enc0 fetched sp hook
    _ = nativeAtAction real source (Route7Sub.Dispatch.selected Rd Rn imm12)
        (decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 0#1 1#1 1#1) enc0
        (actionState (Route7Sub.Dispatch.selected Rd Rn imm12) sp 20) := boundary
    _ = nativeAfterAction real source (Route7Sub.Dispatch.selected Rd Rn imm12) enc0 fin :=
      action_boundary real source (Route7Sub.Dispatch.selected Rd Rn imm12)
        (decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 0#1 1#1 1#1) enc0
        (actionState (Route7Sub.Dispatch.selected Rd Rn imm12) sp 20) fin action

#print axioms action_prefix
end Route7Sub.TailCore
