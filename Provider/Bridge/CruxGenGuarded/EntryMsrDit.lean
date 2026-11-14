import Bridge.CruxGenGuarded.OwnerMetadata
import Bridge.CruxGenGuarded.Action
import NativeEntryInput.Input
import NativeEntryContract.MsrDit
import NativeEntryDispatch.MsrDit
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace ArmBridge.CruxGenGuarded.EntryMsrDit
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
  IO.eprintln "CURRENT_DECL CruxGenGuarded.EntryMsrDit.action_prefix"
  (← IO.getStderr).flush

theorem action_prefix (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rt : BitVec 5) (rt : Rt.toNat < 31)
    (profile : NativeEntryAdapters.MsrDit.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    ∃ sp fin,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntryInput.Input source (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702) ∧
      (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702).mem = fetched.mem ∧
      (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702).events = fetched.events ∧
      nativeTail real source (NativeEntryDispatch.MsrDit.word Rt) enc0 fetched =
        nativeAfterAction real source (NativeEntryDispatch.MsrDit.word Rt) enc0 fin ∧
      NativeEntry.MsrDit.projection fin =
        NativeEntry.MsrDit.expected (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702) Rt ∧
      NativeEntryContract.Frame NativeEntryAdapters.MsrDit.writes
        (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702) fin ∧
      HookQuiet ticks fin ∧ fin.mem = fetched.mem ∧
      fin.events = fetched.events := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryDispatch.MsrDit.word Rt) 702
  have metadataQuiet := actionState_quiet (NativeEntryDispatch.MsrDit.word Rt) sp 702 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntry.MsrDit.Guard (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702) Rt := by
    simpa only [NativeEntryDispatch.MsrDit.effect_word] using NativeEntryAdapters.MsrDit.guard_at_metadata source sp Rt 702 profile currentInput.controls currentPins ticks post.quiet rt
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryContract.MsrDit.run (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702) Rt classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryDispatch.MsrDit.word Rt)
      (decode_msr_reg_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 0#1) 702 := by
    intro pc t see
    exact NativeEntryDispatch.MsrDit.dispatch_at real pc Rt t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryDispatch.MsrDit.word Rt)
    (decode_msr_reg_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 0#1) enc0 sp currentGuard 702 (by decide) dispatch
  have memory : fin.mem = (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702).mem := by
    exact congrArg (fun value => value.2.1) projection
  have events : fin.events = (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702).events := by
    exact congrArg (fun value => value.2.2) projection
  have eventFrame : fin.events = fetched.events := by
    simpa only [actionState_events, post.events] using events
  refine ⟨sp, fin, hook, metadataInput,
    (actionState_mem (NativeEntryDispatch.MsrDit.word Rt) sp 702).trans post.mem,
    (actionState_events (NativeEntryDispatch.MsrDit.word Rt) sp 702).trans post.events,
    ?_, projection, frame, finalQuiet,
    memory.trans ((actionState_mem (NativeEntryDispatch.MsrDit.word Rt) sp 702).trans post.mem), eventFrame⟩
  calc
    nativeTail real source (NativeEntryDispatch.MsrDit.word Rt) enc0 fetched =
        afterSpecPmu real source (NativeEntryDispatch.MsrDit.word Rt) enc0 sp :=
      spec_pmu_boundary real source (NativeEntryDispatch.MsrDit.word Rt) enc0 fetched sp hook
    _ = nativeAtAction real source (NativeEntryDispatch.MsrDit.word Rt)
        (decode_msr_reg_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 0#1) enc0
        (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702) := boundary
    _ = nativeAfterAction real source (NativeEntryDispatch.MsrDit.word Rt) enc0 fin :=
      action_boundary real source (NativeEntryDispatch.MsrDit.word Rt)
        (decode_msr_reg_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 0#1) enc0
        (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702) fin action

#print axioms action_prefix
end ArmBridge.CruxGenGuarded.EntryMsrDit
