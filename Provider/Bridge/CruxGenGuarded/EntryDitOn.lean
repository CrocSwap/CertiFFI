import Bridge.CruxGenGuarded.OwnerMetadata
import Bridge.CruxGenGuarded.Action
import NativeEntryInput.Input
import NativeEntryContract.DitOn
import NativeEntryDispatch.DitOn
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace ArmBridge.CruxGenGuarded.EntryDitOn
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
  IO.eprintln "CURRENT_DECL CruxGenGuarded.EntryDitOn.action_prefix"
  (← IO.getStderr).flush

theorem action_prefix (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (profile : NativeEntryAdapters.DitOn.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    ∃ sp fin,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntryInput.Input source (actionState (NativeEntryDispatch.DitOn.word) sp 703) ∧
      (actionState (NativeEntryDispatch.DitOn.word) sp 703).mem = fetched.mem ∧
      (actionState (NativeEntryDispatch.DitOn.word) sp 703).events = fetched.events ∧
      nativeTail real source (NativeEntryDispatch.DitOn.word) enc0 fetched =
        nativeAfterAction real source (NativeEntryDispatch.DitOn.word) enc0 fin ∧
      NativeEntry.DitOn.projection fin =
        NativeEntry.DitOn.expected (actionState (NativeEntryDispatch.DitOn.word) sp 703) ∧
      NativeEntryContract.Frame NativeEntryAdapters.DitOn.writes
        (actionState (NativeEntryDispatch.DitOn.word) sp 703) fin ∧
      HookQuiet ticks fin ∧ fin.mem = fetched.mem ∧
      fin.events = fetched.events := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryDispatch.DitOn.word) 703
  have metadataQuiet := actionState_quiet (NativeEntryDispatch.DitOn.word) sp 703 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntry.DitOn.Guard (actionState (NativeEntryDispatch.DitOn.word) sp 703) := by
    exact NativeEntryAdapters.DitOn.guard_at_metadata source sp 703 profile currentInput.controls currentPins ticks post.quiet
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryContract.DitOn.run (actionState (NativeEntryDispatch.DitOn.word) sp 703) classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryDispatch.DitOn.word)
      (decode_msr_imm_aarch64_instrs_system_register_cpsr 2#3 1#4 3#3) 703 := by
    intro pc t see
    exact NativeEntryDispatch.DitOn.dispatch_at real pc t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryDispatch.DitOn.word)
    (decode_msr_imm_aarch64_instrs_system_register_cpsr 2#3 1#4 3#3) enc0 sp currentGuard 703 (by decide) dispatch
  have memory : fin.mem = (actionState (NativeEntryDispatch.DitOn.word) sp 703).mem := by
    exact congrArg (fun value => value.2.1) projection
  have events : fin.events = (actionState (NativeEntryDispatch.DitOn.word) sp 703).events := by
    exact congrArg (fun value => value.2.2) projection
  have eventFrame : fin.events = fetched.events := by
    simpa only [actionState_events, post.events] using events
  refine ⟨sp, fin, hook, metadataInput,
    (actionState_mem (NativeEntryDispatch.DitOn.word) sp 703).trans post.mem,
    (actionState_events (NativeEntryDispatch.DitOn.word) sp 703).trans post.events,
    ?_, projection, frame, finalQuiet,
    memory.trans ((actionState_mem (NativeEntryDispatch.DitOn.word) sp 703).trans post.mem), eventFrame⟩
  calc
    nativeTail real source (NativeEntryDispatch.DitOn.word) enc0 fetched =
        afterSpecPmu real source (NativeEntryDispatch.DitOn.word) enc0 sp :=
      spec_pmu_boundary real source (NativeEntryDispatch.DitOn.word) enc0 fetched sp hook
    _ = nativeAtAction real source (NativeEntryDispatch.DitOn.word)
        (decode_msr_imm_aarch64_instrs_system_register_cpsr 2#3 1#4 3#3) enc0
        (actionState (NativeEntryDispatch.DitOn.word) sp 703) := boundary
    _ = nativeAfterAction real source (NativeEntryDispatch.DitOn.word) enc0 fin :=
      action_boundary real source (NativeEntryDispatch.DitOn.word)
        (decode_msr_imm_aarch64_instrs_system_register_cpsr 2#3 1#4 3#3) enc0
        (actionState (NativeEntryDispatch.DitOn.word) sp 703) fin action

#print axioms action_prefix
end ArmBridge.CruxGenGuarded.EntryDitOn
