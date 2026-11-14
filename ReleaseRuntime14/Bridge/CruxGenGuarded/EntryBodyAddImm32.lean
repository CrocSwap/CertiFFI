import Bridge.CruxGenGuarded.OwnerMetadata
import Bridge.CruxGenGuarded.Action
import NativeEntryInput.Input
import NativeEntryBodyContract.AddImm32
import NativeEntryBodyAdapters.AddImm32
import NativeEntryBodyDispatch.AddImm32
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace ArmBridge.CruxGenGuarded.EntryBodyAddImm32
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
  IO.eprintln "CURRENT_DECL CruxGenGuarded.EntryBodyAddImm32.action_prefix"
  (← IO.getStderr).flush

theorem action_prefix (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (imm12 : BitVec 12) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (profile : NativeEntryBodyAdapters.AddImm32.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    ∃ sp fin,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntryInput.Input source (actionState (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) sp 18) ∧
      (actionState (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) sp 18).mem = fetched.mem ∧
      (actionState (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) sp 18).events = fetched.events ∧
      nativeTail real source (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) enc0 fetched =
        nativeAfterAction real source (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) enc0 fin ∧
      NativeEntryBody.AddImm32.projection fin =
        NativeEntryBody.AddImm32.expected (actionState (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) sp 18) Rd Rn imm12 ∧
      NativeEntryContract.Frame NativeEntryBodyAdapters.AddImm32.writes
        (actionState (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) sp 18) fin ∧
      HookQuiet ticks fin ∧ fin.mem = fetched.mem ∧
      fin.events = fetched.events := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) 18
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) sp 18 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntryBody.AddImm32.Guard (actionState (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) sp 18) Rd Rn imm12 := by
    exact NativeEntryBodyAdapters.AddImm32.guard_at_metadata source sp Rd Rn imm12 (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) 18 profile currentInput.controls currentPins ticks post.quiet rd rn
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryBodyContract.AddImm32.run (actionState (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) sp 18) Rd Rn imm12 classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12)
      (decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 0#1 0#1 0#1) 18 := by
    intro pc t see
    exact NativeEntryBodyDispatch.AddImm32.dispatch_at real pc Rd Rn imm12 t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12)
    (decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 0#1 0#1 0#1) enc0 sp currentGuard 18 (by decide) dispatch
  have memory : fin.mem = (actionState (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) sp 18).mem := by
    exact congrArg (fun value => value.2.1) projection
  have events : fin.events = (actionState (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) sp 18).events := by
    exact congrArg (fun value => value.2.2) projection
  have eventFrame : fin.events = fetched.events := by
    simpa only [actionState_events, post.events] using events
  refine ⟨sp, fin, hook, metadataInput,
    (actionState_mem (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) sp 18).trans post.mem,
    (actionState_events (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) sp 18).trans post.events,
    ?_, projection, frame, finalQuiet,
    memory.trans ((actionState_mem (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) sp 18).trans post.mem), eventFrame⟩
  calc
    nativeTail real source (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) enc0 fetched =
        afterSpecPmu real source (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) enc0 sp :=
      spec_pmu_boundary real source (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) enc0 fetched sp hook
    _ = nativeAtAction real source (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12)
        (decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 0#1 0#1 0#1) enc0
        (actionState (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) sp 18) := boundary
    _ = nativeAfterAction real source (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) enc0 fin :=
      action_boundary real source (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12)
        (decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 0#1 0#1 0#1) enc0
        (actionState (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) sp 18) fin action

#print axioms action_prefix
end ArmBridge.CruxGenGuarded.EntryBodyAddImm32
