import Bridge.CruxGenGuarded.OwnerMetadata
import Bridge.CruxGenGuarded.Action
import NativeEntryInput.Input
import NativeEntryBodyFlag.SubsShift64
import Bridge.CruxGenGuarded.EntryControls
import NativeEntryBodyDispatch.SubsShift64
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace ArmBridge.CruxGenGuarded.EntryBodySubsShift64
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
  IO.eprintln "CURRENT_DECL CruxGenGuarded.EntryBodySubsShift64.action_prefix"
  (← IO.getStderr).flush

theorem action_prefix (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (imm6 : BitVec 6)
    (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    ∃ sp fin,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntryInput.Input source (actionState (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) sp 17) ∧
      (actionState (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) sp 17).mem = fetched.mem ∧
      (actionState (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) sp 17).events = fetched.events ∧
      nativeTail real source (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) enc0 fetched =
        nativeAfterAction real source (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) enc0 fin ∧
      fin.regs.BTypeNext = (actionState (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) sp 17).regs.BTypeNext ∧
      NativeEntryContract.Frame NativeEntryBodyFlag.SubsShift64.writes
        (actionState (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) sp 17) fin ∧
      HookQuiet ticks fin ∧ fin.mem = fetched.mem ∧
      fin.events = fetched.events := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) 17
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) sp 17 ticks post.quiet
  have metaPins := entryPins_at_metadata sp (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) 17
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame)
  have classGuard : NativeEntryBodyFlag.SubsShift64.Guard (actionState (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) sp 17) Rd Rn imm6 Rm := by
    constructor <;> first | assumption | exact metaPins.el | exact metaPins.nrw | exact metaPins.f4 | exact metaPins.spe | (show sp.regs.PSTATE.BTYPE = 0#2; rw [(PMUFrame.of_E20 post.frame).pstate]; exact pins.btype) | (show sp.regs.BTypeNext = 0#2; exact (PMUFrame.of_E20 post.frame).btn.trans pins.btn)
  obtain ⟨fin, action, memRun, eventsRun, actFrame, _, frame, finalQuiet⟩ :=
    NativeEntryBodyFlag.SubsShift64.run (actionState (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) sp 17) Rd Rn imm6 Rm classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm)
      (decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm 0#2 1#1 1#1 1#1) 17 := by
    intro pc t see
    exact NativeEntryBodyDispatch.SubsShift64.dispatch_at real pc Rd Rn imm6 Rm t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm)
    (decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm 0#2 1#1 1#1 1#1) enc0 sp currentGuard 17 (by decide) dispatch
  have memory : fin.mem = (actionState (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) sp 17).mem := by
    exact memRun
  have events : fin.events = (actionState (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) sp 17).events := by
    exact eventsRun
  have eventFrame : fin.events = fetched.events := by
    simpa only [actionState_events, post.events] using events
  refine ⟨sp, fin, hook, metadataInput,
    (actionState_mem (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) sp 17).trans post.mem,
    (actionState_events (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) sp 17).trans post.events,
    ?_, actFrame.btn, frame, finalQuiet,
    memory.trans ((actionState_mem (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) sp 17).trans post.mem), eventFrame⟩
  calc
    nativeTail real source (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) enc0 fetched =
        afterSpecPmu real source (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) enc0 sp :=
      spec_pmu_boundary real source (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) enc0 fetched sp hook
    _ = nativeAtAction real source (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm)
        (decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm 0#2 1#1 1#1 1#1) enc0
        (actionState (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) sp 17) := boundary
    _ = nativeAfterAction real source (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) enc0 fin :=
      action_boundary real source (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm)
        (decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm 0#2 1#1 1#1 1#1) enc0
        (actionState (NativeEntryBodyDispatch.SubsShift64.selected Rd Rn imm6 Rm) sp 17) fin action

#print axioms action_prefix
end ArmBridge.CruxGenGuarded.EntryBodySubsShift64
