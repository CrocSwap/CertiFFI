-- RtBr.BcondDecode: B.cond NZCV frame on decode_b_cond.
import SDKPA.Roots
import RtBr.BcondNZCV
import RtBr.BrWords
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
set_option autoImplicit false
namespace RtBr.BcondDecode
open RtBr.BrWords


set_option maxHeartbeats 4000000 in
/-- B.cond (decode level, taken or not) leaves N, Z, C, V unchanged. Sail-only (BR8.BCond + SDKPA.Roots). -/
theorem decode_nzcv (real : Type) [Sail.SailReal real] (cond : BitVec 4) (imm19 : BitVec 19)
    (s u : SequentialState Regs oracleChoiceSource)
    (hBP : Crypto.BranchPinsPA s) (hVHE : s.regs.FeatureImpl[54] = true)
    (hlow : (s.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55)
    (h : (decode_b_cond_aarch64_instrs_branch_conditional_cond cond imm19 : SailM Unit) s = .ok () u) :
    u.regs.PSTATE.N = s.regs.PSTATE.N ∧ u.regs.PSTATE.Z = s.regs.PSTATE.Z ∧
    u.regs.PSTATE.C = s.regs.PSTATE.C ∧ u.regs.PSTATE.V = s.regs.PSTATE.V := by
  rw [BR_BCondH.complete_pa real cond imm19 (bcondWord imm19 cond) (-1)
    s hBP.hFeature_AA32EL0 hBP.hFeature_AA32EL1 hBP.hFeature_AA32EL2 hBP.hFeature_AA32EL3 hBP.hFeature_AA64EL0 hBP.hFeature_AA64EL1 hBP.hFeature_AA64EL2 hBP.hFeature_AA64EL3 hBP.hFeature_AES hBP.hFeature_AFP hBP.hFeature_AdvSIMD hBP.hFeature_BF16 hBP.hFeature_BRBE hBP.hFeature_BTI hBP.hFeature_CRC32 hBP.hFeature_DGH hBP.hFeature_DIT hBP.hFeature_DPB hBP.hFeature_DPB2 hBP.hFeature_Debugv8p9 hBP.hFeature_DotProd hBP.hFeature_ECV hBP.hFeature_FCMA hBP.hFeature_FHM hBP.hFeature_FP hBP.hFeature_FP16 hBP.hFeature_FRINTTS hBP.hFeature_FlagM hBP.hFeature_FlagM2 hBP.hFeature_I8MM hBP.hFeature_JSCVT hBP.hFeature_LRCPC hBP.hFeature_LRCPC2 hBP.hFeature_LSE hBP.hFeature_LSE2 hBP.hFeature_MOPS hBP.hFeature_MTE hBP.hFeature_MTE2 hBP.hFeature_PACIMP hBP.hFeature_PFAR hBP.hFeature_PMULL hBP.hFeature_RDM hBP.hFeature_RME hBP.hFeature_SB hBP.hFeature_SHA1 hBP.hFeature_SHA256 hBP.hFeature_SHA3 hBP.hFeature_SHA512 hBP.hFeature_SM3 hBP.hFeature_SM4 hBP.hFeature_SME hBP.hFeature_SME_F64F64 hBP.hFeature_SME_FA64 hBP.hFeature_SME_I16I64 hBP.hFeature_SVE hBP.hFeature_SVE2 hBP.hFeature_SVE_AES hBP.hFeature_SVE_BitPerm hBP.hFeature_SVE_PMULL128 hBP.hFeature_SVE_SHA3 hBP.hFeature_SVE_SM4 hBP.hFeature_TME hBP.hFeature_WFxT hBP.hDebugBP hBP.hDebugWP hBP.hDebugCTX hBP.hEDSCR_STATUS hBP.hSPE hBP.hEL hBP.hnRW hBP.hIL hBP.hE2H hBP.hTGE hBP.hSCR_NS hBP.hSCR_NSE hBP.hMDSCR_SS hBP.hPSTATE_SS hBP.hOSUC hBP.hPMB_E hBP.hSCR_RW hBP.hSCR_EEL2 hBP.hTBI0 hBP.hTBID0 hBP.hNSPB hBP.hNSPBE
      (bcond_inv imm19 cond) (bcond_inv imm19 cond) (bcond_cond imm19 cond) (bcond_imm19 imm19 cond) (by decide)] at h
  exact RtBr.BcondNZCV.nzcv real cond imm19 _ s hBP hVHE hlow u h

#print axioms decode_nzcv
end RtBr.BcondDecode
