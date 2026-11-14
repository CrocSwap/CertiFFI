-- Chain lever 1: the MTE2-agnostic branch pin bundle, split out of TranslateSpan.BranchMTE2 so the
-- Bcond/Cbz observation proofs can import it without the heavy module. Same namespace; names unchanged.
import Sail
import ArmFull
import BridgeDraft.StateProjection
import Pilot.EvalProfile
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
open ArmBridge.Draft
set_option autoImplicit false
namespace TranslateSpan.BranchMTE2

structure Base (s : NativeState) : Prop where
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
  hEDSCR_STATUS : _get_EDSCR_Type_STATUS (s.regs.bank_BitVec_32 ._EDSCR) = 0b000010#6
  hSPE : s.regs.bank_Bool .SPESampleInFlight = false
  hEL : s.regs.PSTATE.EL = 0#2
  hnRW : s.regs.PSTATE.nRW = 0#1
  hIL : s.regs.PSTATE.IL = 0#1
  hE2H : _get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1
  hTGE : _get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1
  hSCR_NS : _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1
  hSCR_NSE : _get_SCR_EL3_Type_NSE (s.regs.bank_BitVec_64 .SCR_EL3) = 0#1
  hMDSCR_SS : _get_MDSCR_EL1_Type_SS (s.regs.bank_BitVec_64 .MDSCR_EL1) = 0#1
  hPSTATE_SS : s.regs.PSTATE.SS = 0#1
  hOSUC : _get_EDESR_Type_OSUC (s.regs.bank_BitVec_32 .EDESR) = 0#1
  hPMB_E : _get_PMBLIMITR_EL1_Type_E (s.regs.bank_BitVec_64 .PMBLIMITR_EL1) = 0#1
  hSCR_RW : _get_SCR_EL3_Type_RW (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1
  hSCR_EEL2 : _get_SCR_EL3_Type_EEL2 (s.regs.bank_BitVec_64 .SCR_EL3) = 0#1
  hTBI0 : _get_TCR_EL2_Type_TBI0 (s.regs.bank_BitVec_64 .TCR_EL2) = 1#1
  hTBID0 : _get_TCR_EL2_Type_TBID0 (s.regs.bank_BitVec_64 .TCR_EL2) = 0#1
  hNSPB : _get_MDCR_EL3_Type_NSPB (s.regs.bank_BitVec_64 .MDCR_EL3) = 0b11#2
  hNSPBE : _get_MDCR_EL3_Type_NSPBE (s.regs.bank_BitVec_64 .MDCR_EL3) = 0#1

theorem Base.f0 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[0] = false := by simpa [getElem!_def] using h.hFeature_AA32EL0
theorem Base.f1 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[1] = false := by simpa [getElem!_def] using h.hFeature_AA32EL1
theorem Base.f2 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[2] = false := by simpa [getElem!_def] using h.hFeature_AA32EL2
theorem Base.f3 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[3] = false := by simpa [getElem!_def] using h.hFeature_AA32EL3
theorem Base.f4 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[4] = true := by simpa [getElem!_def] using h.hFeature_AA64EL0
theorem Base.f5 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[5] = true := by simpa [getElem!_def] using h.hFeature_AA64EL1
theorem Base.f6 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[6] = true := by simpa [getElem!_def] using h.hFeature_AA64EL2
theorem Base.f7 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[7] = true := by simpa [getElem!_def] using h.hFeature_AA64EL3
theorem Base.f12 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[12] = true := by simpa [getElem!_def] using h.hFeature_AES
theorem Base.f153 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[153] = true := by simpa [getElem!_def] using h.hFeature_AFP
theorem Base.f13 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[13] = true := by simpa [getElem!_def] using h.hFeature_AdvSIMD
theorem Base.f143 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[143] = true := by simpa [getElem!_def] using h.hFeature_BF16
theorem Base.f230 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[230] = false := by simpa [getElem!_def] using h.hFeature_BRBE
theorem Base.f123 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[123] = true := by simpa [getElem!_def] using h.hFeature_BTI
theorem Base.f45 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[45] = true := by simpa [getElem!_def] using h.hFeature_CRC32
theorem Base.f144 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[144] = true := by simpa [getElem!_def] using h.hFeature_DGH
theorem Base.f103 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[103] = true := by simpa [getElem!_def] using h.hFeature_DIT
theorem Base.f60 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[60] = true := by simpa [getElem!_def] using h.hFeature_DPB
theorem Base.f126 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[126] = true := by simpa [getElem!_def] using h.hFeature_DPB2
theorem Base.f185 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[185] = false := by simpa [getElem!_def] using h.hFeature_Debugv8p9
theorem Base.f105 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[105] = true := by simpa [getElem!_def] using h.hFeature_DotProd
theorem Base.f145 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[145] = true := by simpa [getElem!_def] using h.hFeature_ECV
theorem Base.f89 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[89] = true := by simpa [getElem!_def] using h.hFeature_FCMA
theorem Base.f107 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[107] = true := by simpa [getElem!_def] using h.hFeature_FHM
theorem Base.f27 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[27] = true := by simpa [getElem!_def] using h.hFeature_FP
theorem Base.f65 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[65] = true := by simpa [getElem!_def] using h.hFeature_FP16
theorem Base.f130 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[130] = true := by simpa [getElem!_def] using h.hFeature_FRINTTS
theorem Base.f108 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[108] = true := by simpa [getElem!_def] using h.hFeature_FlagM
theorem Base.f131 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[131] = true := by simpa [getElem!_def] using h.hFeature_FlagM2
theorem Base.f67 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[67] = true := by simpa [getElem!_def] using h.hFeature_I8MM
theorem Base.f92 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[92] = true := by simpa [getElem!_def] using h.hFeature_JSCVT
theorem Base.f93 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[93] = true := by simpa [getElem!_def] using h.hFeature_LRCPC
theorem Base.f110 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[110] = true := by simpa [getElem!_def] using h.hFeature_LRCPC2
theorem Base.f50 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[50] = true := by simpa [getElem!_def] using h.hFeature_LSE
theorem Base.f111 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[111] = true := by simpa [getElem!_def] using h.hFeature_LSE2
theorem Base.f171 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[171] = false := by simpa [getElem!_def] using h.hFeature_MOPS
theorem Base.f133 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[133] = true := by simpa [getElem!_def] using h.hFeature_MTE
theorem Base.f95 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[95] = false := by simpa [getElem!_def] using h.hFeature_PACIMP
theorem Base.f200 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[200] = false := by simpa [getElem!_def] using h.hFeature_PFAR
theorem Base.f36 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[36] = true := by simpa [getElem!_def] using h.hFeature_PMULL
theorem Base.f53 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[53] = true := by simpa [getElem!_def] using h.hFeature_RDM
theorem Base.f232 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[232] = false := by simpa [getElem!_def] using h.hFeature_RME
theorem Base.f138 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[138] = true := by simpa [getElem!_def] using h.hFeature_SB
theorem Base.f40 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[40] = true := by simpa [getElem!_def] using h.hFeature_SHA1
theorem Base.f41 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[41] = true := by simpa [getElem!_def] using h.hFeature_SHA256
theorem Base.f76 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[76] = true := by simpa [getElem!_def] using h.hFeature_SHA3
theorem Base.f77 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[77] = true := by simpa [getElem!_def] using h.hFeature_SHA512
theorem Base.f78 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[78] = true := by simpa [getElem!_def] using h.hFeature_SM3
theorem Base.f79 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[79] = true := by simpa [getElem!_def] using h.hFeature_SM4
theorem Base.f233 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[233] = false := by simpa [getElem!_def] using h.hFeature_SME
theorem Base.f234 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[234] = false := by simpa [getElem!_def] using h.hFeature_SME_F64F64
theorem Base.f235 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[235] = false := by simpa [getElem!_def] using h.hFeature_SME_FA64
theorem Base.f236 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[236] = false := by simpa [getElem!_def] using h.hFeature_SME_I16I64
theorem Base.f81 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[81] = true := by simpa [getElem!_def] using h.hFeature_SVE
theorem Base.f221 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[221] = true := by simpa [getElem!_def] using h.hFeature_SVE2
theorem Base.f222 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[222] = true := by simpa [getElem!_def] using h.hFeature_SVE_AES
theorem Base.f223 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[223] = true := by simpa [getElem!_def] using h.hFeature_SVE_BitPerm
theorem Base.f224 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[224] = true := by simpa [getElem!_def] using h.hFeature_SVE_PMULL128
theorem Base.f225 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[225] = true := by simpa [getElem!_def] using h.hFeature_SVE_SHA3
theorem Base.f226 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[226] = true := by simpa [getElem!_def] using h.hFeature_SVE_SM4
theorem Base.f227 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[227] = false := by simpa [getElem!_def] using h.hFeature_TME
theorem Base.f165 {s : SequentialState Regs oracleChoiceSource} (h : Base s) :
    s.regs.FeatureImpl[165] = true := by simpa [getElem!_def] using h.hFeature_WFxT

end TranslateSpan.BranchMTE2
