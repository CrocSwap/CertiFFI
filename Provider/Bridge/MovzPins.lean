import Roots.Movz
import Bridge.Boundary
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions EvalProfile
namespace ArmBridge.Movz

/-- GB10 profile pins: exactly the premise binders of Survey_1f83247d2118106e.complete. -/
structure Pins (s : SequentialState Regs oracleChoiceSource) : Prop where
  hFeature_AA32EL0 : s.regs.FeatureImpl[0]! = false
  hFeature_AA32EL1 : s.regs.FeatureImpl[1]! = false
  hFeature_AA32EL2 : s.regs.FeatureImpl[2]! = false
  hFeature_AA32EL3 : s.regs.FeatureImpl[3]! = false
  hFeature_AA64EL0 : s.regs.FeatureImpl[4]! = true
  hFeature_AA64EL1 : s.regs.FeatureImpl[5]! = true
  hFeature_AA64EL2 : s.regs.FeatureImpl[6]! = true
  hFeature_AA64EL3 : s.regs.FeatureImpl[7]! = true
  hFeature_AES : s.regs.FeatureImpl[12]! = true
  hFeature_AFP : s.regs.FeatureImpl[153]! = true
  hFeature_AdvSIMD : s.regs.FeatureImpl[13]! = true
  hFeature_BF16 : s.regs.FeatureImpl[143]! = true
  hFeature_BRBE : s.regs.FeatureImpl[230]! = false
  hFeature_BTI : s.regs.FeatureImpl[123]! = true
  hFeature_CRC32 : s.regs.FeatureImpl[45]! = true
  hFeature_DGH : s.regs.FeatureImpl[144]! = true
  hFeature_DIT : s.regs.FeatureImpl[103]! = true
  hFeature_DPB : s.regs.FeatureImpl[60]! = true
  hFeature_DPB2 : s.regs.FeatureImpl[126]! = true
  hFeature_Debugv8p9 : s.regs.FeatureImpl[185]! = false
  hFeature_DotProd : s.regs.FeatureImpl[105]! = true
  hFeature_ECV : s.regs.FeatureImpl[145]! = true
  hFeature_FCMA : s.regs.FeatureImpl[89]! = true
  hFeature_FHM : s.regs.FeatureImpl[107]! = true
  hFeature_FP : s.regs.FeatureImpl[27]! = true
  hFeature_FP16 : s.regs.FeatureImpl[65]! = true
  hFeature_FRINTTS : s.regs.FeatureImpl[130]! = true
  hFeature_FlagM : s.regs.FeatureImpl[108]! = true
  hFeature_FlagM2 : s.regs.FeatureImpl[131]! = true
  hFeature_I8MM : s.regs.FeatureImpl[67]! = true
  hFeature_JSCVT : s.regs.FeatureImpl[92]! = true
  hFeature_LRCPC : s.regs.FeatureImpl[93]! = true
  hFeature_LRCPC2 : s.regs.FeatureImpl[110]! = true
  hFeature_LSE : s.regs.FeatureImpl[50]! = true
  hFeature_LSE2 : s.regs.FeatureImpl[111]! = true
  hFeature_MOPS : s.regs.FeatureImpl[171]! = false
  hFeature_MTE : s.regs.FeatureImpl[133]! = true
  hFeature_MTE2 : s.regs.FeatureImpl[134]! = false
  hFeature_PACIMP : s.regs.FeatureImpl[95]! = false
  hFeature_PFAR : s.regs.FeatureImpl[200]! = false
  hFeature_PMULL : s.regs.FeatureImpl[36]! = true
  hFeature_RDM : s.regs.FeatureImpl[53]! = true
  hFeature_RME : s.regs.FeatureImpl[232]! = false
  hFeature_SB : s.regs.FeatureImpl[138]! = true
  hFeature_SHA1 : s.regs.FeatureImpl[40]! = true
  hFeature_SHA256 : s.regs.FeatureImpl[41]! = true
  hFeature_SHA3 : s.regs.FeatureImpl[76]! = true
  hFeature_SHA512 : s.regs.FeatureImpl[77]! = true
  hFeature_SM3 : s.regs.FeatureImpl[78]! = true
  hFeature_SM4 : s.regs.FeatureImpl[79]! = true
  hFeature_SME : s.regs.FeatureImpl[233]! = false
  hFeature_SME_F64F64 : s.regs.FeatureImpl[234]! = false
  hFeature_SME_FA64 : s.regs.FeatureImpl[235]! = false
  hFeature_SME_I16I64 : s.regs.FeatureImpl[236]! = false
  hFeature_SVE : s.regs.FeatureImpl[81]! = true
  hFeature_SVE2 : s.regs.FeatureImpl[221]! = true
  hFeature_SVE_AES : s.regs.FeatureImpl[222]! = true
  hFeature_SVE_BitPerm : s.regs.FeatureImpl[223]! = true
  hFeature_SVE_PMULL128 : s.regs.FeatureImpl[224]! = true
  hFeature_SVE_SHA3 : s.regs.FeatureImpl[225]! = true
  hFeature_SVE_SM4 : s.regs.FeatureImpl[226]! = true
  hFeature_TME : s.regs.FeatureImpl[227]! = false
  hFeature_WFxT : s.regs.FeatureImpl[165]! = true
  hDebugBP : s.regs.bank_Int .NUM_BREAKPOINTS = 6
  hDebugWP : s.regs.bank_Int .NUM_WATCHPOINTS = 4
  hDebugCTX : s.regs.bank_Int .__num_ctx_breakpoints = 2
  hEL : s.regs.PSTATE.EL = 0#2
  hnRW : s.regs.PSTATE.nRW = 0#1
  hSCTLR : s.regs.bank_BitVec_64 .SCTLR_EL1 = sctlrOff
  hTCR : s.regs.bank_BitVec_64 .TCR_EL1 = tcrLinux
  hMAIR : s.regs.bank_BitVec_64 .MAIR_EL1 = mairLinux
  hHCR : s.regs.bank_BitVec_64 .HCR_EL2 = hcrNvhe
  hSCR : s.regs.bank_BitVec_64 .SCR_EL3 = scrEl3
  hMDSCR : s.regs.bank_BitVec_64 .MDSCR_EL1 = 0#64
  hMPAM2 : s.regs.bank_BitVec_64 .MPAM2_EL2 = 0#64
  hMPAM3 : s.regs.bank_BitVec_64 ._MPAM3_EL3 = 0#64
  hEDSCR_STATUS : _get_EDSCR_Type_STATUS (s.regs.bank_BitVec_32 ._EDSCR) = 0b000010#6
  hSPE : s.regs.bank_Bool .SPESampleInFlight = false
  hPA : s.regs.bank_Int .__supported_pa_size = paSize

/-- The published root, rewritten to its native tree under Pins. -/
theorem Pins.root (real : Type) [Sail.SailReal real] (Rd : BitVec 5) (imm16 : BitVec 16) (hw : BitVec 2) (opc : BitVec 2) (sf : BitVec 1) (s : SequentialState Regs oracleChoiceSource) (h : Pins s) :
    decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 hw opc sf s = Survey_1f83247d2118106e.native real Rd imm16 hw opc sf s :=
  Survey_1f83247d2118106e.complete real Rd imm16 hw opc sf s h.hFeature_AA32EL0 h.hFeature_AA32EL1 h.hFeature_AA32EL2 h.hFeature_AA32EL3 h.hFeature_AA64EL0 h.hFeature_AA64EL1 h.hFeature_AA64EL2 h.hFeature_AA64EL3 h.hFeature_AES h.hFeature_AFP h.hFeature_AdvSIMD h.hFeature_BF16 h.hFeature_BRBE h.hFeature_BTI h.hFeature_CRC32 h.hFeature_DGH h.hFeature_DIT h.hFeature_DPB h.hFeature_DPB2 h.hFeature_Debugv8p9 h.hFeature_DotProd h.hFeature_ECV h.hFeature_FCMA h.hFeature_FHM h.hFeature_FP h.hFeature_FP16 h.hFeature_FRINTTS h.hFeature_FlagM h.hFeature_FlagM2 h.hFeature_I8MM h.hFeature_JSCVT h.hFeature_LRCPC h.hFeature_LRCPC2 h.hFeature_LSE h.hFeature_LSE2 h.hFeature_MOPS h.hFeature_MTE h.hFeature_MTE2 h.hFeature_PACIMP h.hFeature_PFAR h.hFeature_PMULL h.hFeature_RDM h.hFeature_RME h.hFeature_SB h.hFeature_SHA1 h.hFeature_SHA256 h.hFeature_SHA3 h.hFeature_SHA512 h.hFeature_SM3 h.hFeature_SM4 h.hFeature_SME h.hFeature_SME_F64F64 h.hFeature_SME_FA64 h.hFeature_SME_I16I64 h.hFeature_SVE h.hFeature_SVE2 h.hFeature_SVE_AES h.hFeature_SVE_BitPerm h.hFeature_SVE_PMULL128 h.hFeature_SVE_SHA3 h.hFeature_SVE_SM4 h.hFeature_TME h.hFeature_WFxT h.hDebugBP h.hDebugWP h.hDebugCTX h.hEL h.hnRW h.hSCTLR h.hTCR h.hMAIR h.hHCR h.hSCR h.hMDSCR h.hMPAM2 h.hMPAM3 h.hEDSCR_STATUS h.hSPE h.hPA

/-- Pins do not mention __BranchTaken. -/
theorem Pins.branchTaken {s : SequentialState Regs oracleChoiceSource} (h : Pins s) (b : Bool) :
    Pins { s with regs := { s.regs with __BranchTaken := b } } :=
  ⟨h.hFeature_AA32EL0, h.hFeature_AA32EL1, h.hFeature_AA32EL2, h.hFeature_AA32EL3, h.hFeature_AA64EL0, h.hFeature_AA64EL1, h.hFeature_AA64EL2, h.hFeature_AA64EL3, h.hFeature_AES, h.hFeature_AFP, h.hFeature_AdvSIMD, h.hFeature_BF16, h.hFeature_BRBE, h.hFeature_BTI, h.hFeature_CRC32, h.hFeature_DGH, h.hFeature_DIT, h.hFeature_DPB, h.hFeature_DPB2, h.hFeature_Debugv8p9, h.hFeature_DotProd, h.hFeature_ECV, h.hFeature_FCMA, h.hFeature_FHM, h.hFeature_FP, h.hFeature_FP16, h.hFeature_FRINTTS, h.hFeature_FlagM, h.hFeature_FlagM2, h.hFeature_I8MM, h.hFeature_JSCVT, h.hFeature_LRCPC, h.hFeature_LRCPC2, h.hFeature_LSE, h.hFeature_LSE2, h.hFeature_MOPS, h.hFeature_MTE, h.hFeature_MTE2, h.hFeature_PACIMP, h.hFeature_PFAR, h.hFeature_PMULL, h.hFeature_RDM, h.hFeature_RME, h.hFeature_SB, h.hFeature_SHA1, h.hFeature_SHA256, h.hFeature_SHA3, h.hFeature_SHA512, h.hFeature_SM3, h.hFeature_SM4, h.hFeature_SME, h.hFeature_SME_F64F64, h.hFeature_SME_FA64, h.hFeature_SME_I16I64, h.hFeature_SVE, h.hFeature_SVE2, h.hFeature_SVE_AES, h.hFeature_SVE_BitPerm, h.hFeature_SVE_PMULL128, h.hFeature_SVE_SHA3, h.hFeature_SVE_SM4, h.hFeature_TME, h.hFeature_WFxT, h.hDebugBP, h.hDebugWP, h.hDebugCTX, h.hEL, h.hnRW, h.hSCTLR, h.hTCR, h.hMAIR, h.hHCR, h.hSCR, h.hMDSCR, h.hMPAM2, h.hMPAM3, h.hEDSCR_STATUS, h.hSPE, h.hPA⟩

/-- The root equation instantiated from Pins. -/
abbrev rootComplete := @Survey_1f83247d2118106e.complete

end ArmBridge.Movz
