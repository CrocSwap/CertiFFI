import Bridge.CruxGenGuarded.OwnerMetadata
import Bridge.CruxGenGuarded.Action
import NativeEntryInput.Input
import NativeEntryBodyContract.SecpCsinv0ZZ
import NativeEntryBodyAdapters.SecpCsinv0ZZ
import NativeEntryBodyDispatch.SecpCsinv0ZZ
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace ArmBridge.CruxGenGuarded.EntryBodySecpCsinv0ZZ
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
  IO.eprintln "CURRENT_DECL CruxGenGuarded.EntryBodySecpCsinv0ZZ.action_prefix"
  (← IO.getStderr).flush

theorem action_prefix (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd : BitVec 5) (rd : Rd.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpCsinv0ZZ.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    ∃ sp fin,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntryInput.Input source (actionState (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) sp 189) ∧
      (actionState (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) sp 189).mem = fetched.mem ∧
      (actionState (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) sp 189).events = fetched.events ∧
      nativeTail real source (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) enc0 fetched =
        nativeAfterAction real source (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) enc0 fin ∧
      NativeEntryBody.SecpCsinv0ZZ.projection fin =
        NativeEntryBody.SecpCsinv0ZZ.expected (actionState (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) sp 189) Rd ∧
      NativeEntryContract.Frame NativeEntryBodyAdapters.SecpCsinv0ZZ.writes
        (actionState (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) sp 189) fin ∧
      HookQuiet ticks fin ∧ fin.mem = fetched.mem ∧
      fin.events = fetched.events := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) 189
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) sp 189 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntryBody.SecpCsinv0ZZ.Guard (actionState (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) sp 189) Rd := by
    exact NativeEntryBodyAdapters.SecpCsinv0ZZ.guard_at_metadata source sp Rd (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) 189 profile currentInput.controls currentPins ticks post.quiet rd
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryBodyContract.SecpCsinv0ZZ.run (actionState (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) sp 189) Rd classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd)
      (decode_csinv_aarch64_instrs_integer_conditional_select Rd 31#5 0#1 0#4 31#5 1#1 1#1) 189 := by
    intro pc t see
    exact NativeEntryBodyDispatch.SecpCsinv0ZZ.dispatch_at real pc Rd t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd)
    (decode_csinv_aarch64_instrs_integer_conditional_select Rd 31#5 0#1 0#4 31#5 1#1 1#1) enc0 sp currentGuard 189 (by decide) dispatch
  have memory : fin.mem = (actionState (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) sp 189).mem := by
    exact congrArg (fun value => value.2.1) projection
  have events : fin.events = (actionState (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) sp 189).events := by
    exact congrArg (fun value => value.2.2) projection
  have eventFrame : fin.events = fetched.events := by
    simpa only [actionState_events, post.events] using events
  refine ⟨sp, fin, hook, metadataInput,
    (actionState_mem (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) sp 189).trans post.mem,
    (actionState_events (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) sp 189).trans post.events,
    ?_, projection, frame, finalQuiet,
    memory.trans ((actionState_mem (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) sp 189).trans post.mem), eventFrame⟩
  calc
    nativeTail real source (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) enc0 fetched =
        afterSpecPmu real source (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) enc0 sp :=
      spec_pmu_boundary real source (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) enc0 fetched sp hook
    _ = nativeAtAction real source (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd)
        (decode_csinv_aarch64_instrs_integer_conditional_select Rd 31#5 0#1 0#4 31#5 1#1 1#1) enc0
        (actionState (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) sp 189) := boundary
    _ = nativeAfterAction real source (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) enc0 fin :=
      action_boundary real source (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd)
        (decode_csinv_aarch64_instrs_integer_conditional_select Rd 31#5 0#1 0#4 31#5 1#1 1#1) enc0
        (actionState (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) sp 189) fin action

#print axioms action_prefix
end ArmBridge.CruxGenGuarded.EntryBodySecpCsinv0ZZ
