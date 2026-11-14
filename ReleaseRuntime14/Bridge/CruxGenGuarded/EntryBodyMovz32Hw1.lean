import Bridge.CruxGenGuarded.OwnerMetadata
import Bridge.CruxGenGuarded.Action
import NativeEntryInput.Input
import NativeEntryBodyContract.Movz32Hw1
import NativeEntryBodyAdapters.Movz32Hw1
import NativeEntryBodyDispatch.Movz32Hw1
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace ArmBridge.CruxGenGuarded.EntryBodyMovz32Hw1
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
  IO.eprintln "CURRENT_DECL CruxGenGuarded.EntryBodyMovz32Hw1.action_prefix"
  (← IO.getStderr).flush

theorem action_prefix (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd : BitVec 5)
    (imm16 : BitVec 16) (rd : Rd.toNat < 31)
    (profile : NativeEntryBodyAdapters.Movz32Hw1.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    ∃ sp fin,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntryInput.Input source (actionState (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) sp 698) ∧
      (actionState (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) sp 698).mem = fetched.mem ∧
      (actionState (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) sp 698).events = fetched.events ∧
      nativeTail real source (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) enc0 fetched =
        nativeAfterAction real source (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) enc0 fin ∧
      NativeEntryBody.Movz32Hw1.projection fin =
        NativeEntryBody.Movz32Hw1.expected (actionState (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) sp 698) Rd imm16 ∧
      NativeEntryContract.Frame NativeEntryBodyAdapters.Movz32Hw1.writes
        (actionState (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) sp 698) fin ∧
      HookQuiet ticks fin ∧ fin.mem = fetched.mem ∧
      fin.events = fetched.events := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) 698
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) sp 698 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntryBody.Movz32Hw1.Guard (actionState (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) sp 698) Rd imm16 := by
    exact NativeEntryBodyAdapters.Movz32Hw1.guard_at_metadata source sp Rd imm16 (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) 698 profile currentInput.controls currentPins ticks post.quiet rd
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryBodyContract.Movz32Hw1.run (actionState (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) sp 698) Rd imm16 classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16)
      (decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 1#2 2#2 0#1) 698 := by
    intro pc t see
    exact NativeEntryBodyDispatch.Movz32Hw1.dispatch_at real pc Rd imm16 t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16)
    (decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 1#2 2#2 0#1) enc0 sp currentGuard 698 (by decide) dispatch
  have memory : fin.mem = (actionState (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) sp 698).mem := by
    exact congrArg (fun value => value.2.1) projection
  have events : fin.events = (actionState (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) sp 698).events := by
    exact congrArg (fun value => value.2.2) projection
  have eventFrame : fin.events = fetched.events := by
    simpa only [actionState_events, post.events] using events
  refine ⟨sp, fin, hook, metadataInput,
    (actionState_mem (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) sp 698).trans post.mem,
    (actionState_events (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) sp 698).trans post.events,
    ?_, projection, frame, finalQuiet,
    memory.trans ((actionState_mem (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) sp 698).trans post.mem), eventFrame⟩
  calc
    nativeTail real source (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) enc0 fetched =
        afterSpecPmu real source (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) enc0 sp :=
      spec_pmu_boundary real source (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) enc0 fetched sp hook
    _ = nativeAtAction real source (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16)
        (decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 1#2 2#2 0#1) enc0
        (actionState (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) sp 698) := boundary
    _ = nativeAfterAction real source (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) enc0 fin :=
      action_boundary real source (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16)
        (decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 1#2 2#2 0#1) enc0
        (actionState (NativeEntryBodyDispatch.Movz32Hw1.selected Rd imm16) sp 698) fin action

#print axioms action_prefix
end ArmBridge.CruxGenGuarded.EntryBodyMovz32Hw1
