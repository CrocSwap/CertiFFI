import Bridge.CruxGenGuarded.OwnerMetadata
import Bridge.CruxGenGuarded.Action
import NativeEntryInput.Input
import NativeEntryBodyContract.SecpAnd64
import NativeEntryBodyAdapters.SecpAnd64
import NativeEntryBodyDispatch.SecpAnd64
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace ArmBridge.CruxGenGuarded.EntryBodySecpAnd64
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
  IO.eprintln "CURRENT_DECL CruxGenGuarded.EntryBodySecpAnd64.action_prefix"
  (← IO.getStderr).flush

theorem action_prefix (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpAnd64.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    ∃ sp fin,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntryInput.Input source (actionState (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) sp 48) ∧
      (actionState (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) sp 48).mem = fetched.mem ∧
      (actionState (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) sp 48).events = fetched.events ∧
      nativeTail real source (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) enc0 fetched =
        nativeAfterAction real source (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) enc0 fin ∧
      NativeEntryBody.SecpAnd64.projection fin =
        NativeEntryBody.SecpAnd64.expected (actionState (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) sp 48) Rd Rn Rm ∧
      NativeEntryContract.Frame NativeEntryBodyAdapters.SecpAnd64.writes
        (actionState (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) sp 48) fin ∧
      HookQuiet ticks fin ∧ fin.mem = fetched.mem ∧
      fin.events = fetched.events := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) 48
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) sp 48 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntryBody.SecpAnd64.Guard (actionState (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) sp 48) Rd Rn Rm := by
    exact NativeEntryBodyAdapters.SecpAnd64.guard_at_metadata source sp Rd Rn Rm (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) 48 profile currentInput.controls currentPins ticks post.quiet rd rn rm
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryBodyContract.SecpAnd64.run (actionState (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) sp 48) Rd Rn Rm classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm)
      (decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 0#2 1#1) 48 := by
    intro pc t see
    exact NativeEntryBodyDispatch.SecpAnd64.dispatch_at real pc Rd Rn Rm t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm)
    (decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 0#2 1#1) enc0 sp currentGuard 48 (by decide) dispatch
  have memory : fin.mem = (actionState (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) sp 48).mem := by
    exact congrArg (fun value => value.2.1) projection
  have events : fin.events = (actionState (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) sp 48).events := by
    exact congrArg (fun value => value.2.2) projection
  have eventFrame : fin.events = fetched.events := by
    simpa only [actionState_events, post.events] using events
  refine ⟨sp, fin, hook, metadataInput,
    (actionState_mem (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) sp 48).trans post.mem,
    (actionState_events (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) sp 48).trans post.events,
    ?_, projection, frame, finalQuiet,
    memory.trans ((actionState_mem (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) sp 48).trans post.mem), eventFrame⟩
  calc
    nativeTail real source (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) enc0 fetched =
        afterSpecPmu real source (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) enc0 sp :=
      spec_pmu_boundary real source (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) enc0 fetched sp hook
    _ = nativeAtAction real source (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm)
        (decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 0#2 1#1) enc0
        (actionState (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) sp 48) := boundary
    _ = nativeAfterAction real source (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) enc0 fin :=
      action_boundary real source (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm)
        (decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 0#2 1#1) enc0
        (actionState (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) sp 48) fin action

#print axioms action_prefix
end ArmBridge.CruxGenGuarded.EntryBodySecpAnd64
