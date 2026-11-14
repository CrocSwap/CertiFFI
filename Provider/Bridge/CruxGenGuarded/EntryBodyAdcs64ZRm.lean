import Bridge.CruxGenGuarded.OwnerMetadata
import Bridge.CruxGenGuarded.Action
import NativeEntryInput.Input
import NativeEntryBodyFlag.Adcs64ZRm
import Bridge.CruxGenGuarded.EntryControls
import NativeEntryBodyDispatch.Adcs64ZRm
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace ArmBridge.CruxGenGuarded.EntryBodyAdcs64ZRm
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
  IO.eprintln "CURRENT_DECL CruxGenGuarded.EntryBodyAdcs64ZRm.action_prefix"
  (← IO.getStderr).flush

theorem action_prefix (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd : BitVec 5)
    (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    ∃ sp fin,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntryInput.Input source (actionState (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) sp 7) ∧
      (actionState (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) sp 7).mem = fetched.mem ∧
      (actionState (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) sp 7).events = fetched.events ∧
      nativeTail real source (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) enc0 fetched =
        nativeAfterAction real source (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) enc0 fin ∧
      fin.regs.BTypeNext = (actionState (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) sp 7).regs.BTypeNext ∧
      NativeEntryContract.Frame NativeEntryBodyFlag.Adcs64ZRm.writes
        (actionState (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) sp 7) fin ∧
      HookQuiet ticks fin ∧ fin.mem = fetched.mem ∧
      fin.events = fetched.events := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) 7
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) sp 7 ticks post.quiet
  have metaPins := entryPins_at_metadata sp (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) 7
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame)
  have classGuard : NativeEntryBodyFlag.Adcs64ZRm.Guard (actionState (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) sp 7) Rd Rn := by
    constructor <;> first | assumption | exact metaPins.el | exact metaPins.nrw | exact metaPins.f4 | exact metaPins.spe | (show sp.regs.PSTATE.BTYPE = 0#2; rw [(PMUFrame.of_E20 post.frame).pstate]; exact pins.btype) | (show sp.regs.BTypeNext = 0#2; exact (PMUFrame.of_E20 post.frame).btn.trans pins.btn)
  obtain ⟨fin, action, memRun, eventsRun, actFrame, _, frame, finalQuiet⟩ :=
    NativeEntryBodyFlag.Adcs64ZRm.run (actionState (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) sp 7) Rd Rn classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn)
      (decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 1#1 0#1 1#1) 7 := by
    intro pc t see
    exact NativeEntryBodyDispatch.Adcs64ZRm.dispatch_at real pc Rd Rn t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn)
    (decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 1#1 0#1 1#1) enc0 sp currentGuard 7 (by decide) dispatch
  have memory : fin.mem = (actionState (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) sp 7).mem := by
    exact memRun
  have events : fin.events = (actionState (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) sp 7).events := by
    exact eventsRun
  have eventFrame : fin.events = fetched.events := by
    simpa only [actionState_events, post.events] using events
  refine ⟨sp, fin, hook, metadataInput,
    (actionState_mem (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) sp 7).trans post.mem,
    (actionState_events (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) sp 7).trans post.events,
    ?_, actFrame.btn, frame, finalQuiet,
    memory.trans ((actionState_mem (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) sp 7).trans post.mem), eventFrame⟩
  calc
    nativeTail real source (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) enc0 fetched =
        afterSpecPmu real source (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) enc0 sp :=
      spec_pmu_boundary real source (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) enc0 fetched sp hook
    _ = nativeAtAction real source (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn)
        (decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 1#1 0#1 1#1) enc0
        (actionState (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) sp 7) := boundary
    _ = nativeAfterAction real source (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) enc0 fin :=
      action_boundary real source (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn)
        (decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 1#1 0#1 1#1) enc0
        (actionState (NativeEntryBodyDispatch.Adcs64ZRm.selected Rd Rn) sp 7) fin action

#print axioms action_prefix
end ArmBridge.CruxGenGuarded.EntryBodyAdcs64ZRm
