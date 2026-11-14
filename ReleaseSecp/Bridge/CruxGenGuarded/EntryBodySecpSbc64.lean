import Bridge.CruxGenGuarded.OwnerMetadata
import Bridge.CruxGenGuarded.Action
import NativeEntryInput.Input
import NativeEntryBodyContract.SecpSbc64
import NativeEntryBodyAdapters.SecpSbc64
import NativeEntryBodyDispatch.SecpSbc64
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace ArmBridge.CruxGenGuarded.EntryBodySecpSbc64
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
  IO.eprintln "CURRENT_DECL CruxGenGuarded.EntryBodySecpSbc64.action_prefix"
  (← IO.getStderr).flush

theorem action_prefix (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpSbc64.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    ∃ sp fin,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntryInput.Input source (actionState (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) sp 8) ∧
      (actionState (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) sp 8).mem = fetched.mem ∧
      (actionState (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) sp 8).events = fetched.events ∧
      nativeTail real source (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) enc0 fetched =
        nativeAfterAction real source (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) enc0 fin ∧
      NativeEntryBody.SecpSbc64.projection fin =
        NativeEntryBody.SecpSbc64.expected (actionState (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) sp 8) Rd Rn Rm ∧
      NativeEntryContract.Frame NativeEntryBodyAdapters.SecpSbc64.writes
        (actionState (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) sp 8) fin ∧
      HookQuiet ticks fin ∧ fin.mem = fetched.mem ∧
      fin.events = fetched.events := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) 8
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) sp 8 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntryBody.SecpSbc64.Guard (actionState (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) sp 8) Rd Rn Rm := by
    exact NativeEntryBodyAdapters.SecpSbc64.guard_at_metadata source sp Rd Rn Rm (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) 8 profile currentInput.controls currentPins ticks post.quiet rd rn rm
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryBodyContract.SecpSbc64.run (actionState (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) sp 8) Rd Rn Rm classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm)
      (decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 0#1 1#1 1#1) 8 := by
    intro pc t see
    exact NativeEntryBodyDispatch.SecpSbc64.dispatch_at real pc Rd Rn Rm t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm)
    (decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 0#1 1#1 1#1) enc0 sp currentGuard 8 (by decide) dispatch
  have memory : fin.mem = (actionState (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) sp 8).mem := by
    exact congrArg (fun value => value.2.1) projection
  have events : fin.events = (actionState (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) sp 8).events := by
    exact congrArg (fun value => value.2.2) projection
  have eventFrame : fin.events = fetched.events := by
    simpa only [actionState_events, post.events] using events
  refine ⟨sp, fin, hook, metadataInput,
    (actionState_mem (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) sp 8).trans post.mem,
    (actionState_events (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) sp 8).trans post.events,
    ?_, projection, frame, finalQuiet,
    memory.trans ((actionState_mem (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) sp 8).trans post.mem), eventFrame⟩
  calc
    nativeTail real source (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) enc0 fetched =
        afterSpecPmu real source (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) enc0 sp :=
      spec_pmu_boundary real source (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) enc0 fetched sp hook
    _ = nativeAtAction real source (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm)
        (decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 0#1 1#1 1#1) enc0
        (actionState (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) sp 8) := boundary
    _ = nativeAfterAction real source (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) enc0 fin :=
      action_boundary real source (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm)
        (decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 0#1 1#1 1#1) enc0
        (actionState (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) sp 8) fin action

#print axioms action_prefix
end ArmBridge.CruxGenGuarded.EntryBodySecpSbc64
