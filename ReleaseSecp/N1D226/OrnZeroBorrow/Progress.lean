import N1D226.OrnZeroBorrow.Tail
import N1D226.OrnZeroBorrow.ExprValue
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace N1D226.OrnZeroBorrow.Progress
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false

/-- Neutral internal progress, constructed from the actual decoder producer. -/
theorem action_prefix (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc) (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (pins : StepPins fetched) (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    ∃ sp act,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntryInput.Input source (actionState (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) sp 54) ∧
      N1D226.OrnZeroBorrow.projection act = N1D226.OrnZeroBorrow.expected (actionState (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) sp 54) Rd Rn imm6 Rm ∧
      NativeEntryContract.Frame {} (actionState (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) sp 54) act ∧
      HookQuiet ticks act ∧
      ((decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm 1#1 0#2 1#2 1#1) : SailM Unit) (actionState (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) sp 54) = .ok () act ∧
      nativeTail real source (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) enc0 fetched = nativeAfterAction real source (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) enc0 act ∧
      act.mem = fetched.mem ∧ act.events = fetched.events := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by rw [← input.ps]; exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) 54
  have metadataQuiet := actionState_quiet (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) sp 54 ticks post.quiet
  have metadataPins := metadata_pins (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) sp 54 (e20_pins fetched sp pins post.frame)
  obtain ⟨act, action, projection, frame, actionQuiet, actionMem, actionEvents, btn⟩ :=
    N1D226.OrnZeroBorrow.Frame.run (actionState (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) sp 54) Rd Rn imm6 Rm rd rn rm metadataPins ticks metadataQuiet
  have boundary := metadata_boundary_at real source (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) (decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm 1#1 0#2 1#2 1#1) enc0 sp currentGuard
    54 (by decide) (N1D226.OrnZeroBorrow.Tail.dispatch real Rd Rn imm6 Rm)
  have actualPrefix : nativeTail real source (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) enc0 fetched =
      nativeAfterAction real source (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) enc0 act := by
    calc
      nativeTail real source (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) enc0 fetched = afterSpecPmu real source (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) enc0 sp :=
        spec_pmu_boundary real source (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) enc0 fetched sp hook
      _ = nativeAtAction real source (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) (decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm 1#1 0#2 1#2 1#1) enc0 (actionState (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) sp 54) := boundary
      _ = nativeAfterAction real source (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) enc0 act :=
        action_boundary real source (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) (decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm 1#1 0#2 1#2 1#1) enc0 (actionState (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) sp 54) act action
  exact ⟨sp, act, hook, metadataInput, projection, frame, actionQuiet, action, actualPrefix,
    actionMem.trans ((actionState_mem (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) sp 54).trans post.mem),
    actionEvents.trans ((actionState_events (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) sp 54).trans post.events)⟩

#print axioms action_prefix

open ArmCertValue HeapV2StepCerts
open HeapV2StepCerts.RegBind (Reg regVal rk)
open N1D226.OrnZeroBorrow.ExprValue

/-- Transfer the existing typed Expr value to this exact actual final state. -/
theorem g_holds_of_native (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc) (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (pins : StepPins fetched) (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (budget : Nat) (quiet : HookQuiet (budget+1) fetched)
    (it : fetched.regs.ShouldAdvanceIT = false) (ss : fetched.regs.ShouldAdvanceSS = true)
    (view : Physical.BytePA) (regions : List Region)
    (fin : NativeState) (run : nativeTail real source (N1D226.OrnZeroBorrow.Encoding.selected Rd Rn imm6 Rm) enc0 fetched = .ok () fin) :
    G.Holds view regions (.reg (.x (rk Rd)) (term Rd Rn imm6 Rm)) fetched fin := by
  obtain ⟨other, actual, holds, _⟩ := N1D226.OrnZeroBorrow.ExprValue.native_G real source fetched enc0 Rd Rn imm6 Rm rd rn rm pins input guard budget quiet it ss view regions
  have same : other = fin := (EStateM.Result.ok.inj (actual.symm.trans run)).2
  exact same ▸ holds

#print axioms g_holds_of_native

end N1D226.OrnZeroBorrow.Progress
