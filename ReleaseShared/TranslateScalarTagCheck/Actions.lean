import TranslateScalarTagCheck.Automation
import TranslateSpan.BranchMTE2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register TagCheckFrames
open ArmBridge.Draft
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
set_option Elab.async false
namespace TranslateScalarTagCheck.Actions


theorem branch_to_preserves (target : BitVec 64) (branch : BranchType) (conditional : Bool) :
    Preserves (BranchTo target branch conditional) := by
  scalar_oracle_frame

#print axioms branch_to_preserves

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

theorem action_0 (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) : Preserves (decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 0#1 0#1 1#1) := by
  unfold decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry execute_aarch64_instrs_integer_arithmetic_add_sub_carry
  scalar_oracle_frame
#print axioms action_0

theorem action_1 (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) : Preserves (decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1) := by
  unfold decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry execute_aarch64_instrs_integer_arithmetic_add_sub_carry
  scalar_oracle_frame
#print axioms action_1

theorem action_2 (Rd : BitVec 5) (Rn : BitVec 5) (imm12 : BitVec 12) : Preserves (decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 0#1 0#1 1#1) := by
  unfold decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate execute_aarch64_instrs_integer_arithmetic_add_sub_immediate
  scalar_oracle_frame
#print axioms action_2

theorem action_3 (Rd : BitVec 5) (Rn : BitVec 5) (imm12 : BitVec 12) : Preserves (decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 1#1 0#1 1#1) := by
  unfold decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate execute_aarch64_instrs_integer_arithmetic_add_sub_immediate
  scalar_oracle_frame
#print axioms action_3

theorem action_4 (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) : Preserves (decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm 0#2 1#1 0#1 1#1) := by
  unfold decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
  scalar_oracle_frame
#print axioms action_4

theorem action_5 (Rd : BitVec 5) (Rn : BitVec 5) (imms : BitVec 6) (immr : BitVec 6) : Preserves (decode_and_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr 1#1 0#2 1#1) := by
  unfold decode_and_log_imm_aarch64_instrs_integer_logical_immediate execute_aarch64_instrs_integer_logical_immediate
  scalar_oracle_frame
#print axioms action_5

theorem action_6 (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) : Preserves (decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm 0#1 0#2 0#2 1#1) := by
  unfold decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg execute_aarch64_instrs_integer_logical_shiftedreg
  scalar_oracle_frame
#print axioms action_6

theorem action_7 (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) : Preserves (decode_bic_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm 1#1 0#2 0#2 1#1) := by
  unfold decode_bic_log_shift_aarch64_instrs_integer_logical_shiftedreg execute_aarch64_instrs_integer_logical_shiftedreg
  scalar_oracle_frame
#print axioms action_7

theorem action_8 (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) : Preserves (decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 1#4 Rm 0#1 1#1) := by
  unfold decode_csel_aarch64_instrs_integer_conditional_select execute_aarch64_instrs_integer_conditional_select
  scalar_oracle_frame
#print axioms action_8

theorem action_9 (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) : Preserves (decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 3#4 Rm 0#1 1#1) := by
  unfold decode_csel_aarch64_instrs_integer_conditional_select execute_aarch64_instrs_integer_conditional_select
  scalar_oracle_frame
#print axioms action_9

theorem action_10 (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) : Preserves (decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn 1#1 3#4 Rm 0#1 1#1) := by
  unfold decode_csinc_aarch64_instrs_integer_conditional_select execute_aarch64_instrs_integer_conditional_select
  scalar_oracle_frame
#print axioms action_10

theorem action_11 (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) : Preserves (decode_csinv_aarch64_instrs_integer_conditional_select Rd Rn 0#1 0#4 Rm 1#1 1#1) := by
  unfold decode_csinv_aarch64_instrs_integer_conditional_select execute_aarch64_instrs_integer_conditional_select
  scalar_oracle_frame
#print axioms action_11

theorem action_12 (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) : Preserves (decode_csinv_aarch64_instrs_integer_conditional_select Rd Rn 0#1 2#4 Rm 1#1 1#1) := by
  unfold decode_csinv_aarch64_instrs_integer_conditional_select execute_aarch64_instrs_integer_conditional_select
  scalar_oracle_frame
#print axioms action_12

theorem action_13 (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) : Preserves (decode_csneg_aarch64_instrs_integer_conditional_select Rd Rn 1#1 2#4 Rm 1#1 1#1) := by
  unfold decode_csneg_aarch64_instrs_integer_conditional_select execute_aarch64_instrs_integer_conditional_select
  scalar_oracle_frame
#print axioms action_13

theorem action_14 (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) : Preserves (decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm 0#1 0#2 2#2 1#1) := by
  unfold decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg execute_aarch64_instrs_integer_logical_shiftedreg
  scalar_oracle_frame
#print axioms action_14

theorem action_15 (Rd : BitVec 5) (Rn : BitVec 5) (imms : BitVec 6) (Rm : BitVec 5) : Preserves (decode_extr_aarch64_instrs_integer_ins_ext_extract_immediate Rd Rn imms Rm 1#1 1#1) := by
  unfold decode_extr_aarch64_instrs_integer_ins_ext_extract_immediate execute_aarch64_instrs_integer_ins_ext_extract_immediate
  scalar_oracle_frame
#print axioms action_15

theorem action_16 (Rd : BitVec 5) (Rn : BitVec 5) (Ra : BitVec 5) (Rm : BitVec 5) : Preserves (decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub Rd Rn Ra 0#1 Rm 1#1) := by
  unfold decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub execute_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub
  scalar_oracle_frame
#print axioms action_16

theorem action_17 (Rd : BitVec 5) (imm16 : BitVec 16) : Preserves (decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 0#2 2#2 1#1) := by
  unfold decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide execute_aarch64_instrs_integer_ins_ext_insert_movewide
  scalar_oracle_frame
#print axioms action_17

theorem action_18 (Rd : BitVec 5) (Rn : BitVec 5) (imms : BitVec 6) (immr : BitVec 6) : Preserves (decode_orr_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr 1#1 1#2 1#1) := by
  unfold decode_orr_log_imm_aarch64_instrs_integer_logical_immediate execute_aarch64_instrs_integer_logical_immediate
  scalar_oracle_frame
#print axioms action_18

theorem action_19 (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) : Preserves (decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm 0#1 0#2 1#2 1#1) := by
  unfold decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg execute_aarch64_instrs_integer_logical_shiftedreg
  scalar_oracle_frame
#print axioms action_19

theorem action_20 (Rn : BitVec 5) (hRn : Rn.toNat < 31) (s : NativeState)
    (gcs : s.regs.FeatureImpl[245] = false) :
    ∀ value after, (decode_ret_aarch64_instrs_branch_unconditional_register 0#5 Rn 0#1 0#1 2#2 0#1) s = .ok value after → NativeMteTagCheck.ChoiceDelta s after 0 :=
  ret_choice Rn hRn s gcs
#print axioms action_20

theorem action_21 (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) : Preserves (decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 0#1 1#1 1#1) := by
  unfold decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry execute_aarch64_instrs_integer_arithmetic_add_sub_carry
  scalar_oracle_frame
#print axioms action_21

theorem action_22 (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) : Preserves (decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 1#1 1#1) := by
  unfold decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry execute_aarch64_instrs_integer_arithmetic_add_sub_carry
  scalar_oracle_frame
#print axioms action_22

theorem action_23 (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) : Preserves (decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm 0#2 1#1 1#1 1#1) := by
  unfold decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
  scalar_oracle_frame
#print axioms action_23

theorem action_24 (Rd : BitVec 5) (Rn : BitVec 5) (imms : BitVec 6) (immr : BitVec 6) : Preserves (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn imms immr 1#1 2#2 1#1) := by
  unfold decode_ubfm_aarch64_instrs_integer_bitfield execute_aarch64_instrs_integer_bitfield
  scalar_oracle_frame
#print axioms action_24

theorem action_25 (Rd : BitVec 5) (Rn : BitVec 5) (Ra : BitVec 5) (Rm : BitVec 5) : Preserves (decode_umaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 Rd Rn Ra 0#1 Rm 1#1) := by
  unfold decode_umaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 execute_aarch64_instrs_integer_arithmetic_mul_widening_32_64
  scalar_oracle_frame
#print axioms action_25

theorem action_26 (Rd : BitVec 5) (Rn : BitVec 5) (Ra : BitVec 5) (Rm : BitVec 5) : Preserves (decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn Ra Rm 1#1) := by
  unfold decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi execute_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi
  scalar_oracle_frame
#print axioms action_26

theorem action_27 (Rd : BitVec 5) : Preserves (decode_csinc_aarch64_instrs_integer_conditional_select Rd 31#5 1#1 1#4 31#5 0#1 0#1) := by
  unfold decode_csinc_aarch64_instrs_integer_conditional_select execute_aarch64_instrs_integer_conditional_select
  scalar_oracle_frame
#print axioms action_27

theorem action_28 (Rn : BitVec 5) (imm12 : BitVec 12) : Preserves (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 Rn imm12 0#1 1#1 1#1 1#1) := by
  unfold decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate execute_aarch64_instrs_integer_arithmetic_add_sub_immediate
  scalar_oracle_frame
#print axioms action_28

theorem action_29 (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) : Preserves (decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 1#1 0#2 1#2 1#1) := by
  unfold decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg execute_aarch64_instrs_integer_logical_shiftedreg
  scalar_oracle_frame
#print axioms action_29

theorem action_30 (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) : Preserves (decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn 0#6 Rm 0#2 0#1 1#1 1#1) := by
  unfold decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
  scalar_oracle_frame
#print axioms action_30

theorem action_31 (Rd : BitVec 5) (Rn : BitVec 5) (imm12 : BitVec 12) : Preserves (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 1#1 1#1 1#1) := by
  unfold decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate execute_aarch64_instrs_integer_arithmetic_add_sub_immediate
  scalar_oracle_frame
#print axioms action_31

theorem action_32 (Rd : BitVec 5) (Rn : BitVec 5) (imms : BitVec 6) (immr : BitVec 6) : Preserves (decode_ands_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr 1#1 3#2 1#1) := by
  unfold decode_ands_log_imm_aarch64_instrs_integer_logical_immediate execute_aarch64_instrs_integer_logical_immediate
  scalar_oracle_frame
#print axioms action_32

theorem action_33 (Rd : BitVec 5) (Rn : BitVec 5) (imm12 : BitVec 12) : Preserves (decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 0#1 1#1 1#1) := by
  unfold decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate execute_aarch64_instrs_integer_arithmetic_add_sub_immediate
  scalar_oracle_frame
#print axioms action_33

theorem action_34 (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) : Preserves (decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm 1#1 0#2 1#2 1#1) := by
  unfold decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg execute_aarch64_instrs_integer_logical_shiftedreg
  scalar_oracle_frame
#print axioms action_34

theorem action_35 (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) : Preserves (decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm 0#2 0#1 1#1 1#1) := by
  unfold decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
  scalar_oracle_frame
#print axioms action_35

end TranslateScalarTagCheck.Actions
