import Bridge.CruxGenGuarded.OwnerMetadata
import Bridge.CruxGenGuarded.Action
import NativeEntryInput.Input
import NativeEntryBodyContract.SecpLsr32
import NativeEntryBodyAdapters.SecpLsr32
import NativeEntryBodyDispatch.SecpLsr32
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace ArmBridge.CruxGenGuarded.EntryBodySecpLsr32
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/- Internal fixed-class action-prefix composition over canonical states.
No initial/current memory identity or caller future action/guard is supplied.
Fetch/input/guard construction, actual tail/modelStep and landing remain open.
BTI alone permits arbitrary incoming BTYPE/BTN; the other class pin requirements
are explicit internal preconditions to derive from the actual protected phase. -/
run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.EntryBodySecpLsr32.action_prefix"
  (← IO.getStderr).flush

theorem action_prefix (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd : BitVec 5)
    (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpLsr32.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    ∃ sp fin,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntryInput.Input source (actionState (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) sp 78) ∧
      (actionState (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) sp 78).mem = fetched.mem ∧
      (actionState (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) sp 78).events = fetched.events ∧
      nativeTail real source (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) enc0 fetched =
        nativeAfterAction real source (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) enc0 fin ∧
      NativeEntryBody.SecpLsr32.projection fin =
        NativeEntryBody.SecpLsr32.expected (actionState (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) sp 78) Rd Rn ∧
      NativeEntryContract.Frame NativeEntryBodyAdapters.SecpLsr32.writes
        (actionState (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) sp 78) fin ∧
      HookQuiet ticks fin ∧ fin.mem = fetched.mem ∧
      fin.events = fetched.events := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) 78
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) sp 78 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntryBody.SecpLsr32.Guard (actionState (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) sp 78) Rd Rn := by
    exact NativeEntryBodyAdapters.SecpLsr32.guard_at_metadata source sp Rd Rn (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) 78 profile currentInput.controls currentPins ticks post.quiet rd rn
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryBodyContract.SecpLsr32.run (actionState (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) sp 78) Rd Rn classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn)
      (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 32#6 1#1 2#2 1#1) 78 := by
    intro pc t see
    exact NativeEntryBodyDispatch.SecpLsr32.dispatch_at real pc Rd Rn t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn)
    (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 32#6 1#1 2#2 1#1) enc0 sp currentGuard 78 (by decide) dispatch
  have memory : fin.mem = (actionState (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) sp 78).mem := by
    exact congrArg (fun value => value.2.1) projection
  have events : fin.events = (actionState (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) sp 78).events := by
    exact congrArg (fun value => value.2.2) projection
  have eventFrame : fin.events = fetched.events := by
    simpa only [actionState_events, post.events] using events
  refine ⟨sp, fin, hook, metadataInput,
    (actionState_mem (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) sp 78).trans post.mem,
    (actionState_events (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) sp 78).trans post.events,
    ?_, projection, frame, finalQuiet,
    memory.trans ((actionState_mem (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) sp 78).trans post.mem), eventFrame⟩
  calc
    nativeTail real source (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) enc0 fetched =
        afterSpecPmu real source (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) enc0 sp :=
      spec_pmu_boundary real source (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) enc0 fetched sp hook
    _ = nativeAtAction real source (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn)
        (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 32#6 1#1 2#2 1#1) enc0
        (actionState (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) sp 78) := boundary
    _ = nativeAfterAction real source (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) enc0 fin :=
      action_boundary real source (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn)
        (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 32#6 1#1 2#2 1#1) enc0
        (actionState (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) sp 78) fin action

#print axioms action_prefix
end ArmBridge.CruxGenGuarded.EntryBodySecpLsr32
