import Bridge.CruxGenGuarded.OwnerMetadata
import Bridge.CruxGenGuarded.Action
import NativeEntryInput.Input
import NativeEntryBodyContract.OrrImm32_0
import NativeEntryBodyAdapters.OrrImm32_0
import NativeEntryBodyDispatch.OrrImm32_0
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace ArmBridge.CruxGenGuarded.EntryBodyOrrImm32_0
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
  IO.eprintln "CURRENT_DECL CruxGenGuarded.EntryBodyOrrImm32_0.action_prefix"
  (← IO.getStderr).flush

theorem action_prefix (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd : BitVec 5)
    (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (profile : NativeEntryBodyAdapters.OrrImm32_0.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    ∃ sp fin,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntryInput.Input source (actionState (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) sp 43) ∧
      (actionState (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) sp 43).mem = fetched.mem ∧
      (actionState (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) sp 43).events = fetched.events ∧
      nativeTail real source (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) enc0 fetched =
        nativeAfterAction real source (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) enc0 fin ∧
      NativeEntryBody.OrrImm32_0.projection fin =
        NativeEntryBody.OrrImm32_0.expected (actionState (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) sp 43) Rd Rn ∧
      NativeEntryContract.Frame NativeEntryBodyAdapters.OrrImm32_0.writes
        (actionState (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) sp 43) fin ∧
      HookQuiet ticks fin ∧ fin.mem = fetched.mem ∧
      fin.events = fetched.events := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) 43
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) sp 43 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntryBody.OrrImm32_0.Guard (actionState (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) sp 43) Rd Rn := by
    exact NativeEntryBodyAdapters.OrrImm32_0.guard_at_metadata source sp Rd Rn (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) 43 profile currentInput.controls currentPins ticks post.quiet rd rn
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryBodyContract.OrrImm32_0.run (actionState (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) sp 43) Rd Rn classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn)
      (decode_orr_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn 0#6 32#6 1#1 1#2 1#1) 43 := by
    intro pc t see
    exact NativeEntryBodyDispatch.OrrImm32_0.dispatch_at real pc Rd Rn t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn)
    (decode_orr_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn 0#6 32#6 1#1 1#2 1#1) enc0 sp currentGuard 43 (by decide) dispatch
  have memory : fin.mem = (actionState (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) sp 43).mem := by
    exact congrArg (fun value => value.2.1) projection
  have events : fin.events = (actionState (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) sp 43).events := by
    exact congrArg (fun value => value.2.2) projection
  have eventFrame : fin.events = fetched.events := by
    simpa only [actionState_events, post.events] using events
  refine ⟨sp, fin, hook, metadataInput,
    (actionState_mem (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) sp 43).trans post.mem,
    (actionState_events (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) sp 43).trans post.events,
    ?_, projection, frame, finalQuiet,
    memory.trans ((actionState_mem (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) sp 43).trans post.mem), eventFrame⟩
  calc
    nativeTail real source (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) enc0 fetched =
        afterSpecPmu real source (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) enc0 sp :=
      spec_pmu_boundary real source (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) enc0 fetched sp hook
    _ = nativeAtAction real source (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn)
        (decode_orr_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn 0#6 32#6 1#1 1#2 1#1) enc0
        (actionState (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) sp 43) := boundary
    _ = nativeAfterAction real source (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) enc0 fin :=
      action_boundary real source (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn)
        (decode_orr_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn 0#6 32#6 1#1 1#2 1#1) enc0
        (actionState (NativeEntryBodyDispatch.OrrImm32_0.selected Rd Rn) sp 43) fin action

#print axioms action_prefix
end ArmBridge.CruxGenGuarded.EntryBodyOrrImm32_0
