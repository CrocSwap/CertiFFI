import DefaultBranchChoice
import NativeEntryCallerParts.BlCall
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft TagCheckFrames NativeEntryCallerParts
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 1024
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

namespace ReleaseProfile.DefaultCallChoice

#check "CURRENT_DECL branch destination source and counter"
theorem branch_to_preserves (target : BitVec 64) (branch : BranchType) (conditional : Bool) :
    Preserves (BranchTo target branch conditional) := by
  scalar_oracle_frame

#print axioms branch_to_preserves

#check "CURRENT_DECL caller prefix source and counter"
theorem bl_before_choice (imm26 : BitVec 26) (s : NativeState) :
    NativeMteTagCheck.ChoiceDelta s (blBeforeCall imm26 s) 0 := by
  exact ⟨rfl, rfl⟩

#print axioms bl_before_choice

#check "CURRENT_DECL actual BL source and counter"
theorem bl_choice (imm26 : BitVec 26) (s : NativeState) (controls : CallerControls s)
    (low : (blTarget imm26 s).toNat < 2^55) :
    NativeMteTagCheck.ChoiceDelta s (blActionState imm26 s) 0 := by
  have actual := branch_run (blTarget imm26 s) BranchType.BranchType_DIRCALL
    (blBeforeCall imm26 s) (bl_controls imm26 s controls) (low_bit55 _ low)
  have delta := branch_to_preserves (blTarget imm26 s) BranchType.BranchType_DIRCALL false
    (blBeforeCall imm26 s) () (blActionState imm26 s) actual
  simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans (bl_before_choice imm26 s) delta

#print axioms bl_choice

theorem ret_choice (Rn : BitVec 5) (hRn : Rn.toNat < 31) (s : NativeState)
    (gcs : s.regs.FeatureImpl[245] = false) (value : Unit) (after : NativeState)
    (run : decode_ret_aarch64_instrs_branch_unconditional_register 0#5 Rn 0#1 0#1 2#2 0#1 s = .ok value after) :
    NativeMteTagCheck.ChoiceDelta s after 0 := by
  unfold decode_ret_aarch64_instrs_branch_unconditional_register execute_aarch64_instrs_branch_unconditional_register at run
  have htn : Sail.Int.toNatChecked ((Rn.toNat : Nat) : Int) = Rn.toNat := rfl
  simp (config := {decide := true}) only [undefined_BranchType, undefined_GCSInstruction, PreSail.internal_pick_at,
    PreSail.chooseAt, PreSail.choose, PreSail.occLabel, modifyGet, Functor.map, EStateM.map, MonadStateOf.modifyGet,
    EStateM.modifyGet, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, bind, EStateM.bind, ite_true,
    ite_false, Bool.false_eq_true, Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_and, Bool.true_and,
    Bool.and_true, beq_self_eq_true, htn] at run
  simp only [Crypto.BrRegs.xread64 _ Rn hRn] at run
  have wrBTN : ∀ (st : NativeState) (v : BitVec 2), (writeReg BTypeNext v : SailM Unit) st =
      .ok () { st with regs := { st.regs with BTypeNext := v } } := fun _ _ => rfl
  simp (config := {decide := true}) only [Crypto.BrRegs.gcs_off, gcs, wrBTN, EStateM.bind, EStateM.pure, ite_false,
    ite_true, Bool.false_eq_true, beq_self_eq_true] at run
  have delta := branch_to_preserves _ _ _ _ _ _ run
  simpa [NativeMteTagCheck.ChoiceDelta, Std.ExtHashMap.getD_insert] using delta

#print axioms ret_choice
end ReleaseProfile.DefaultCallChoice
