import SDKPA.BranchPins
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions EvalProfile
namespace Crypto

/-- The feature pins of BranchPinsPA in `[k]` (bounds-checked getElem) form. -/
theorem BranchPinsPA.f0 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[0] = false := by simpa [getElem!_def] using h.hFeature_AA32EL0
theorem BranchPinsPA.f1 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[1] = false := by simpa [getElem!_def] using h.hFeature_AA32EL1
theorem BranchPinsPA.f2 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[2] = false := by simpa [getElem!_def] using h.hFeature_AA32EL2
theorem BranchPinsPA.f3 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[3] = false := by simpa [getElem!_def] using h.hFeature_AA32EL3
theorem BranchPinsPA.f4 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[4] = true := by simpa [getElem!_def] using h.hFeature_AA64EL0
theorem BranchPinsPA.f5 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[5] = true := by simpa [getElem!_def] using h.hFeature_AA64EL1
theorem BranchPinsPA.f6 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[6] = true := by simpa [getElem!_def] using h.hFeature_AA64EL2
theorem BranchPinsPA.f7 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[7] = true := by simpa [getElem!_def] using h.hFeature_AA64EL3
theorem BranchPinsPA.f12 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[12] = true := by simpa [getElem!_def] using h.hFeature_AES
theorem BranchPinsPA.f153 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[153] = true := by simpa [getElem!_def] using h.hFeature_AFP
theorem BranchPinsPA.f13 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[13] = true := by simpa [getElem!_def] using h.hFeature_AdvSIMD
theorem BranchPinsPA.f143 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[143] = true := by simpa [getElem!_def] using h.hFeature_BF16
theorem BranchPinsPA.f230 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[230] = false := by simpa [getElem!_def] using h.hFeature_BRBE
theorem BranchPinsPA.f123 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[123] = true := by simpa [getElem!_def] using h.hFeature_BTI
theorem BranchPinsPA.f45 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[45] = true := by simpa [getElem!_def] using h.hFeature_CRC32
theorem BranchPinsPA.f144 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[144] = true := by simpa [getElem!_def] using h.hFeature_DGH
theorem BranchPinsPA.f103 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[103] = true := by simpa [getElem!_def] using h.hFeature_DIT
theorem BranchPinsPA.f60 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[60] = true := by simpa [getElem!_def] using h.hFeature_DPB
theorem BranchPinsPA.f126 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[126] = true := by simpa [getElem!_def] using h.hFeature_DPB2
theorem BranchPinsPA.f185 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[185] = false := by simpa [getElem!_def] using h.hFeature_Debugv8p9
theorem BranchPinsPA.f105 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[105] = true := by simpa [getElem!_def] using h.hFeature_DotProd
theorem BranchPinsPA.f145 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[145] = true := by simpa [getElem!_def] using h.hFeature_ECV
theorem BranchPinsPA.f89 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[89] = true := by simpa [getElem!_def] using h.hFeature_FCMA
theorem BranchPinsPA.f107 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[107] = true := by simpa [getElem!_def] using h.hFeature_FHM
theorem BranchPinsPA.f27 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[27] = true := by simpa [getElem!_def] using h.hFeature_FP
theorem BranchPinsPA.f65 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[65] = true := by simpa [getElem!_def] using h.hFeature_FP16
theorem BranchPinsPA.f130 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[130] = true := by simpa [getElem!_def] using h.hFeature_FRINTTS
theorem BranchPinsPA.f108 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[108] = true := by simpa [getElem!_def] using h.hFeature_FlagM
theorem BranchPinsPA.f131 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[131] = true := by simpa [getElem!_def] using h.hFeature_FlagM2
theorem BranchPinsPA.f67 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[67] = true := by simpa [getElem!_def] using h.hFeature_I8MM
theorem BranchPinsPA.f92 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[92] = true := by simpa [getElem!_def] using h.hFeature_JSCVT
theorem BranchPinsPA.f93 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[93] = true := by simpa [getElem!_def] using h.hFeature_LRCPC
theorem BranchPinsPA.f110 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[110] = true := by simpa [getElem!_def] using h.hFeature_LRCPC2
theorem BranchPinsPA.f50 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[50] = true := by simpa [getElem!_def] using h.hFeature_LSE
theorem BranchPinsPA.f111 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[111] = true := by simpa [getElem!_def] using h.hFeature_LSE2
theorem BranchPinsPA.f171 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[171] = false := by simpa [getElem!_def] using h.hFeature_MOPS
theorem BranchPinsPA.f133 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[133] = true := by simpa [getElem!_def] using h.hFeature_MTE
theorem BranchPinsPA.f134 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[134] = false := by simpa [getElem!_def] using h.hFeature_MTE2
theorem BranchPinsPA.f95 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[95] = false := by simpa [getElem!_def] using h.hFeature_PACIMP
theorem BranchPinsPA.f200 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[200] = false := by simpa [getElem!_def] using h.hFeature_PFAR
theorem BranchPinsPA.f36 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[36] = true := by simpa [getElem!_def] using h.hFeature_PMULL
theorem BranchPinsPA.f53 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[53] = true := by simpa [getElem!_def] using h.hFeature_RDM
theorem BranchPinsPA.f232 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[232] = false := by simpa [getElem!_def] using h.hFeature_RME
theorem BranchPinsPA.f138 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[138] = true := by simpa [getElem!_def] using h.hFeature_SB
theorem BranchPinsPA.f40 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[40] = true := by simpa [getElem!_def] using h.hFeature_SHA1
theorem BranchPinsPA.f41 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[41] = true := by simpa [getElem!_def] using h.hFeature_SHA256
theorem BranchPinsPA.f76 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[76] = true := by simpa [getElem!_def] using h.hFeature_SHA3
theorem BranchPinsPA.f77 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[77] = true := by simpa [getElem!_def] using h.hFeature_SHA512
theorem BranchPinsPA.f78 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[78] = true := by simpa [getElem!_def] using h.hFeature_SM3
theorem BranchPinsPA.f79 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[79] = true := by simpa [getElem!_def] using h.hFeature_SM4
theorem BranchPinsPA.f233 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[233] = false := by simpa [getElem!_def] using h.hFeature_SME
theorem BranchPinsPA.f234 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[234] = false := by simpa [getElem!_def] using h.hFeature_SME_F64F64
theorem BranchPinsPA.f235 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[235] = false := by simpa [getElem!_def] using h.hFeature_SME_FA64
theorem BranchPinsPA.f236 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[236] = false := by simpa [getElem!_def] using h.hFeature_SME_I16I64
theorem BranchPinsPA.f81 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[81] = true := by simpa [getElem!_def] using h.hFeature_SVE
theorem BranchPinsPA.f221 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[221] = true := by simpa [getElem!_def] using h.hFeature_SVE2
theorem BranchPinsPA.f222 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[222] = true := by simpa [getElem!_def] using h.hFeature_SVE_AES
theorem BranchPinsPA.f223 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[223] = true := by simpa [getElem!_def] using h.hFeature_SVE_BitPerm
theorem BranchPinsPA.f224 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[224] = true := by simpa [getElem!_def] using h.hFeature_SVE_PMULL128
theorem BranchPinsPA.f225 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[225] = true := by simpa [getElem!_def] using h.hFeature_SVE_SHA3
theorem BranchPinsPA.f226 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[226] = true := by simpa [getElem!_def] using h.hFeature_SVE_SM4
theorem BranchPinsPA.f227 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[227] = false := by simpa [getElem!_def] using h.hFeature_TME
theorem BranchPinsPA.f165 {s : SequentialState Regs oracleChoiceSource} (h : BranchPinsPA s) :
    s.regs.FeatureImpl[165] = true := by simpa [getElem!_def] using h.hFeature_WFxT

end Crypto
