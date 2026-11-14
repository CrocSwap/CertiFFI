import N1D226.CsetEq32.Tail
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace N1D226.CsetEq32.Progress
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false

/-- Neutral internal progress, constructed from the actual decoder producer. -/
theorem action_prefix (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc) (Rd : BitVec 5) (rd : Rd.toNat < 31)
    (pins : StepPins fetched) (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    ∃ sp act,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntryInput.Input source (actionState (N1D226.CsetEq32.Encoding.selected Rd) sp 188) ∧
      N1D226.CsetEq32.projection act = N1D226.CsetEq32.expected (actionState (N1D226.CsetEq32.Encoding.selected Rd) sp 188) Rd ∧
      NativeEntryContract.Frame {} (actionState (N1D226.CsetEq32.Encoding.selected Rd) sp 188) act ∧
      HookQuiet ticks act ∧
      ((decode_csinc_aarch64_instrs_integer_conditional_select Rd 31#5 1#1 1#4 31#5 0#1 0#1) : SailM Unit) (actionState (N1D226.CsetEq32.Encoding.selected Rd) sp 188) = .ok () act ∧
      nativeTail real source (N1D226.CsetEq32.Encoding.selected Rd) enc0 fetched = nativeAfterAction real source (N1D226.CsetEq32.Encoding.selected Rd) enc0 act ∧
      act.mem = fetched.mem ∧ act.events = fetched.events := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by rw [← input.ps]; exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (N1D226.CsetEq32.Encoding.selected Rd) 188
  have metadataQuiet := actionState_quiet (N1D226.CsetEq32.Encoding.selected Rd) sp 188 ticks post.quiet
  have metadataPins := metadata_pins (N1D226.CsetEq32.Encoding.selected Rd) sp 188 (e20_pins fetched sp pins post.frame)
  obtain ⟨act, action, projection, frame, actionQuiet, actionMem, actionEvents, btn⟩ :=
    N1D226.CsetEq32.Frame.run (actionState (N1D226.CsetEq32.Encoding.selected Rd) sp 188) Rd rd metadataPins ticks metadataQuiet
  have boundary := metadata_boundary_at real source (N1D226.CsetEq32.Encoding.selected Rd) (decode_csinc_aarch64_instrs_integer_conditional_select Rd 31#5 1#1 1#4 31#5 0#1 0#1) enc0 sp currentGuard
    188 (by decide) (N1D226.CsetEq32.Tail.dispatch real Rd)
  have actualPrefix : nativeTail real source (N1D226.CsetEq32.Encoding.selected Rd) enc0 fetched =
      nativeAfterAction real source (N1D226.CsetEq32.Encoding.selected Rd) enc0 act := by
    calc
      nativeTail real source (N1D226.CsetEq32.Encoding.selected Rd) enc0 fetched = afterSpecPmu real source (N1D226.CsetEq32.Encoding.selected Rd) enc0 sp :=
        spec_pmu_boundary real source (N1D226.CsetEq32.Encoding.selected Rd) enc0 fetched sp hook
      _ = nativeAtAction real source (N1D226.CsetEq32.Encoding.selected Rd) (decode_csinc_aarch64_instrs_integer_conditional_select Rd 31#5 1#1 1#4 31#5 0#1 0#1) enc0 (actionState (N1D226.CsetEq32.Encoding.selected Rd) sp 188) := boundary
      _ = nativeAfterAction real source (N1D226.CsetEq32.Encoding.selected Rd) enc0 act :=
        action_boundary real source (N1D226.CsetEq32.Encoding.selected Rd) (decode_csinc_aarch64_instrs_integer_conditional_select Rd 31#5 1#1 1#4 31#5 0#1 0#1) enc0 (actionState (N1D226.CsetEq32.Encoding.selected Rd) sp 188) act action
  exact ⟨sp, act, hook, metadataInput, projection, frame, actionQuiet, action, actualPrefix,
    actionMem.trans ((actionState_mem (N1D226.CsetEq32.Encoding.selected Rd) sp 188).trans post.mem),
    actionEvents.trans ((actionState_events (N1D226.CsetEq32.Encoding.selected Rd) sp 188).trans post.events)⟩

#print axioms action_prefix

end N1D226.CsetEq32.Progress
