-- BR8 split B1 (post-seal branch): PA-free rewrite of an opaque BranchTo call.
import BR8.BranchToPins
import SDKPA.Roots
import SDKPA.BranchPins
set_option autoImplicit false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace RtBr.BrToRwPA
theorem brto_rw_pa {S : SequentialState Regs oracleChoiceSource} (hB : Crypto.BranchPinsPA S)
    (t : BitVec 64) (bt : BranchType) (c : Bool) (hV : S.regs.FeatureImpl[54] = true) (hlow : t.toNat < 2 ^ 55) :
    (BranchTo t bt c : SailM Unit) S = BR8_BranchTo.native t bt c S :=
  BR8_BranchTo.complete_pa t bt c S hB.hFeature_AA32EL0 hB.hFeature_AA32EL1 hB.hFeature_AA32EL2 hB.hFeature_AA32EL3 hB.hFeature_AA64EL0 hB.hFeature_AA64EL1 hB.hFeature_AA64EL2 hB.hFeature_AA64EL3 hB.hFeature_AES hB.hFeature_AFP hB.hFeature_AdvSIMD hB.hFeature_BF16 hB.hFeature_BRBE hB.hFeature_BTI hB.hFeature_CRC32 hB.hFeature_DGH hB.hFeature_DIT hB.hFeature_DPB hB.hFeature_DPB2 hB.hFeature_Debugv8p9 hB.hFeature_DotProd hB.hFeature_ECV hB.hFeature_FCMA hB.hFeature_FHM hB.hFeature_FP hB.hFeature_FP16 hB.hFeature_FRINTTS hB.hFeature_FlagM hB.hFeature_FlagM2 hB.hFeature_I8MM hB.hFeature_JSCVT hB.hFeature_LRCPC hB.hFeature_LRCPC2 hB.hFeature_LSE hB.hFeature_LSE2 hB.hFeature_MOPS hB.hFeature_MTE hB.hFeature_MTE2 hB.hFeature_PACIMP hB.hFeature_PFAR hB.hFeature_PMULL hB.hFeature_RDM hB.hFeature_RME hB.hFeature_SB hB.hFeature_SHA1 hB.hFeature_SHA256 hB.hFeature_SHA3 hB.hFeature_SHA512 hB.hFeature_SM3 hB.hFeature_SM4 hB.hFeature_SME hB.hFeature_SME_F64F64 hB.hFeature_SME_FA64 hB.hFeature_SME_I16I64 hB.hFeature_SVE hB.hFeature_SVE2 hB.hFeature_SVE_AES hB.hFeature_SVE_BitPerm hB.hFeature_SVE_PMULL128 hB.hFeature_SVE_SHA3 hB.hFeature_SVE_SM4 hB.hFeature_TME hB.hFeature_WFxT hB.hDebugBP hB.hDebugWP hB.hDebugCTX hB.hEDSCR_STATUS hB.hSPE hB.hEL hB.hnRW hB.hIL hB.hE2H hB.hTGE hB.hSCR_NS hB.hSCR_NSE hB.hMDSCR_SS hB.hPSTATE_SS hB.hOSUC hB.hPMB_E hB.hSCR_RW hB.hSCR_EEL2 hB.hTBI0 hB.hTBID0 hB.hNSPB hB.hNSPBE (BR8Pins.vhe_bang _ hV) (BR8Pins.bit55_of_lt _ hlow)
end RtBr.BrToRwPA
