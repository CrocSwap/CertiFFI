import HeapScalarTagCheck.Automation
import TranslateSpan.BranchMTE2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register TagCheckFrames
open ArmBridge.Draft
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option Elab.async false
namespace HeapScalarTagCheck.Actions

theorem action_0 (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) : Preserves (decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 0#1 0#1 1#1) := by
  unfold decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry execute_aarch64_instrs_integer_arithmetic_add_sub_carry
  scalar_oracle_frame
#print axioms action_0

#print axioms action_0

theorem action_1 (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) : Preserves (decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1) := by
  unfold decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry execute_aarch64_instrs_integer_arithmetic_add_sub_carry
  scalar_oracle_frame
#print axioms action_1

#print axioms action_1

theorem action_2 (Rd : BitVec 5) (Rn : BitVec 5) (imm12 : BitVec 12) : Preserves (decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 0#1 0#1 1#1) := by
  unfold decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate execute_aarch64_instrs_integer_arithmetic_add_sub_immediate
  scalar_oracle_frame
#print axioms action_2

#print axioms action_2

theorem action_4 (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) : Preserves (decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm 0#2 1#1 0#1 1#1) := by
  unfold decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
  scalar_oracle_frame
#print axioms action_4

#print axioms action_4

theorem action_9 (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) : Preserves (decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 3#4 Rm 0#1 1#1) := by
  unfold decode_csel_aarch64_instrs_integer_conditional_select execute_aarch64_instrs_integer_conditional_select
  scalar_oracle_frame
#print axioms action_9

#print axioms action_9

theorem action_10 (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) : Preserves (decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn 1#1 3#4 Rm 0#1 1#1) := by
  unfold decode_csinc_aarch64_instrs_integer_conditional_select execute_aarch64_instrs_integer_conditional_select
  scalar_oracle_frame
#print axioms action_10

#print axioms action_10

theorem action_16 (Rd : BitVec 5) (Rn : BitVec 5) (Ra : BitVec 5) (Rm : BitVec 5) : Preserves (decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub Rd Rn Ra 0#1 Rm 1#1) := by
  unfold decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub execute_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub
  scalar_oracle_frame
#print axioms action_16

#print axioms action_16

theorem action_17 (Rd : BitVec 5) (imm16 : BitVec 16) : Preserves (decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 0#2 2#2 1#1) := by
  unfold decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide execute_aarch64_instrs_integer_ins_ext_insert_movewide
  scalar_oracle_frame
#print axioms action_17

#print axioms action_17

theorem action_18 (Rd : BitVec 5) (Rn : BitVec 5) (imms : BitVec 6) (immr : BitVec 6) : Preserves (decode_orr_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr 1#1 1#2 1#1) := by
  unfold decode_orr_log_imm_aarch64_instrs_integer_logical_immediate execute_aarch64_instrs_integer_logical_immediate
  scalar_oracle_frame
#print axioms action_18

#print axioms action_18

theorem action_19 (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) : Preserves (decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm 0#1 0#2 1#2 1#1) := by
  unfold decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg execute_aarch64_instrs_integer_logical_shiftedreg
  scalar_oracle_frame
#print axioms action_19

#print axioms action_19

theorem action_21 (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) : Preserves (decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 0#1 1#1 1#1) := by
  unfold decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry execute_aarch64_instrs_integer_arithmetic_add_sub_carry
  scalar_oracle_frame
#print axioms action_21

#print axioms action_21

theorem action_22 (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) : Preserves (decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 1#1 1#1) := by
  unfold decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry execute_aarch64_instrs_integer_arithmetic_add_sub_carry
  scalar_oracle_frame
#print axioms action_22

#print axioms action_22

theorem action_23 (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) : Preserves (decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm 0#2 1#1 1#1 1#1) := by
  unfold decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
  scalar_oracle_frame
#print axioms action_23

#print axioms action_23

theorem action_26 (Rd : BitVec 5) (Rn : BitVec 5) (Ra : BitVec 5) (Rm : BitVec 5) : Preserves (decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn Ra Rm 1#1) := by
  unfold decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi execute_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi
  scalar_oracle_frame
#print axioms action_26

#print axioms action_26

theorem action_28 (Rn : BitVec 5) (imm12 : BitVec 12) : Preserves (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 Rn imm12 0#1 1#1 1#1 1#1) := by
  unfold decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate execute_aarch64_instrs_integer_arithmetic_add_sub_immediate
  scalar_oracle_frame
#print axioms action_28

#print axioms action_28

theorem action_31 (Rd : BitVec 5) (Rn : BitVec 5) (imm12 : BitVec 12) : Preserves (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 1#1 1#1 1#1) := by
  unfold decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate execute_aarch64_instrs_integer_arithmetic_add_sub_immediate
  scalar_oracle_frame
#print axioms action_31

#print axioms action_31

theorem action_32 (Rd : BitVec 5) (Rn : BitVec 5) (imms : BitVec 6) (immr : BitVec 6) : Preserves (decode_ands_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr 1#1 3#2 1#1) := by
  unfold decode_ands_log_imm_aarch64_instrs_integer_logical_immediate execute_aarch64_instrs_integer_logical_immediate
  scalar_oracle_frame
#print axioms action_32

#print axioms action_32

theorem action_33 (Rd : BitVec 5) (Rn : BitVec 5) (imm12 : BitVec 12) : Preserves (decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 0#1 1#1 1#1) := by
  unfold decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate execute_aarch64_instrs_integer_arithmetic_add_sub_immediate
  scalar_oracle_frame
#print axioms action_33

#print axioms action_33

end HeapScalarTagCheck.Actions
