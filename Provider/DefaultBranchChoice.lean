import HeapScalarTagCheck.Actions
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open TagCheckFrames
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

namespace ReleaseProfile.DefaultBranchChoice

#check "CURRENT_DECL conditional branch choice"
theorem bcond (cond : BitVec 4) (imm19 : BitVec 19) :
    Preserves (decode_b_cond_aarch64_instrs_branch_conditional_cond cond imm19) := by
  unfold decode_b_cond_aarch64_instrs_branch_conditional_cond
  scalar_oracle_frame

#print axioms bcond

#check "CURRENT_DECL compare branch choice"
theorem cbz (Rt : BitVec 5) (imm19 : BitVec 19) (op sf : BitVec 1) :
    Preserves (decode_cbz_aarch64_instrs_branch_conditional_compare Rt imm19 op sf) := by
  unfold decode_cbz_aarch64_instrs_branch_conditional_compare
  scalar_oracle_frame

#print axioms cbz

end ReleaseProfile.DefaultBranchChoice
