import Bridge.CruxGenGuarded.OwnerMetadata
import Bridge.CruxGenGuarded.Action
import NativeEntryInput.Input
import NativeEntryContract.BtiC
import NativeEntryDispatch.BtiC
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace ArmBridge.CruxGenGuarded.EntryBtiC
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
  IO.eprintln "CURRENT_DECL CruxGenGuarded.EntryBtiC.action_prefix"
  (← IO.getStderr).flush

theorem action_prefix (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    ∃ sp fin,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntryInput.Input source (actionState (NativeEntryDispatch.BtiC.word) sp 97) ∧
      (actionState (NativeEntryDispatch.BtiC.word) sp 97).mem = fetched.mem ∧
      (actionState (NativeEntryDispatch.BtiC.word) sp 97).events = fetched.events ∧
      nativeTail real source (NativeEntryDispatch.BtiC.word) enc0 fetched =
        nativeAfterAction real source (NativeEntryDispatch.BtiC.word) enc0 fin ∧
      NativeEntry.BtiC.projection fin =
        NativeEntry.BtiC.expected (actionState (NativeEntryDispatch.BtiC.word) sp 97) ∧
      NativeEntryContract.Frame NativeEntryAdapters.BtiC.writes
        (actionState (NativeEntryDispatch.BtiC.word) sp 97) fin ∧
      HookQuiet ticks fin ∧ fin.mem = fetched.mem ∧
      fin.events = fetched.events := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryDispatch.BtiC.word) 97
  have metadataQuiet := actionState_quiet (NativeEntryDispatch.BtiC.word) sp 97 ticks post.quiet

  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryContract.BtiC.run (actionState (NativeEntryDispatch.BtiC.word) sp 97) ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryDispatch.BtiC.word)
      (decode_bti_aarch64_instrs_system_hints 2#3 4#4) 97 := by
    intro pc t see
    exact NativeEntryDispatch.BtiC.dispatch_at real pc t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryDispatch.BtiC.word)
    (decode_bti_aarch64_instrs_system_hints 2#3 4#4) enc0 sp currentGuard 97 (by decide) dispatch
  have memory : fin.mem = (actionState (NativeEntryDispatch.BtiC.word) sp 97).mem := by
    exact congrArg (fun value => value.2.1) projection
  have events : fin.events = (actionState (NativeEntryDispatch.BtiC.word) sp 97).events := by
    exact congrArg (fun value => value.2.2) projection
  have eventFrame : fin.events = fetched.events := by
    simpa only [actionState_events, post.events] using events
  refine ⟨sp, fin, hook, metadataInput,
    (actionState_mem (NativeEntryDispatch.BtiC.word) sp 97).trans post.mem,
    (actionState_events (NativeEntryDispatch.BtiC.word) sp 97).trans post.events,
    ?_, projection, frame, finalQuiet,
    memory.trans ((actionState_mem (NativeEntryDispatch.BtiC.word) sp 97).trans post.mem), eventFrame⟩
  calc
    nativeTail real source (NativeEntryDispatch.BtiC.word) enc0 fetched =
        afterSpecPmu real source (NativeEntryDispatch.BtiC.word) enc0 sp :=
      spec_pmu_boundary real source (NativeEntryDispatch.BtiC.word) enc0 fetched sp hook
    _ = nativeAtAction real source (NativeEntryDispatch.BtiC.word)
        (decode_bti_aarch64_instrs_system_hints 2#3 4#4) enc0
        (actionState (NativeEntryDispatch.BtiC.word) sp 97) := boundary
    _ = nativeAfterAction real source (NativeEntryDispatch.BtiC.word) enc0 fin :=
      action_boundary real source (NativeEntryDispatch.BtiC.word)
        (decode_bti_aarch64_instrs_system_hints 2#3 4#4) enc0
        (actionState (NativeEntryDispatch.BtiC.word) sp 97) fin action

#print axioms action_prefix
end ArmBridge.CruxGenGuarded.EntryBtiC
