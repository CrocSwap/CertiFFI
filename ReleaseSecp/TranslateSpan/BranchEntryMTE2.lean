-- Exact scalar branch fields; the action proof does not read MTE2.
import TranslateSpan.BranchMTE2
import TranslateSpan.EntryControls
open Sail ArmFull ArmFull.Functions ArmBridge.Draft
open ArmBridge.CruxGenGuarded.EntryActualFetch
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.BranchEntryMTE2

def check (s : NativeState) : Bool :=
  ((((((decide (s.regs.FeatureImpl[0] = false) &&
    decide (s.regs.FeatureImpl[1] = false)) &&
    (decide (s.regs.FeatureImpl[2] = false) &&
    (decide (s.regs.FeatureImpl[3] = false) &&
    decide (s.regs.FeatureImpl[4] = true)))) &&
    ((decide (s.regs.FeatureImpl[5] = true) &&
    decide (s.regs.FeatureImpl[6] = true)) &&
    (decide (s.regs.FeatureImpl[7] = true) &&
    (decide (s.regs.FeatureImpl[12] = true) &&
    decide (s.regs.FeatureImpl[153] = true))))) &&
    (((decide (s.regs.FeatureImpl[13] = true) &&
    decide (s.regs.FeatureImpl[143] = true)) &&
    (decide (s.regs.FeatureImpl[230] = false) &&
    (decide (s.regs.FeatureImpl[123] = true) &&
    decide (s.regs.FeatureImpl[45] = true)))) &&
    ((decide (s.regs.FeatureImpl[144] = true) &&
    (decide (s.regs.FeatureImpl[103] = true) &&
    decide (s.regs.FeatureImpl[60] = true))) &&
    (decide (s.regs.FeatureImpl[126] = true) &&
    (decide (s.regs.FeatureImpl[185] = false) &&
    decide (s.regs.FeatureImpl[105] = true)))))) &&
    ((((decide (s.regs.FeatureImpl[145] = true) &&
    decide (s.regs.FeatureImpl[89] = true)) &&
    (decide (s.regs.FeatureImpl[107] = true) &&
    (decide (s.regs.FeatureImpl[27] = true) &&
    decide (s.regs.FeatureImpl[65] = true)))) &&
    ((decide (s.regs.FeatureImpl[130] = true) &&
    decide (s.regs.FeatureImpl[108] = true)) &&
    (decide (s.regs.FeatureImpl[131] = true) &&
    (decide (s.regs.FeatureImpl[67] = true) &&
    decide (s.regs.FeatureImpl[92] = true))))) &&
    (((decide (s.regs.FeatureImpl[93] = true) &&
    decide (s.regs.FeatureImpl[110] = true)) &&
    (decide (s.regs.FeatureImpl[50] = true) &&
    (decide (s.regs.FeatureImpl[111] = true) &&
    decide (s.regs.FeatureImpl[171] = false)))) &&
    ((decide (s.regs.FeatureImpl[133] = true) &&
    (decide (s.regs.FeatureImpl[95] = false) &&
    decide (s.regs.FeatureImpl[200] = false))) &&
    (decide (s.regs.FeatureImpl[36] = true) &&
    (decide (s.regs.FeatureImpl[53] = true) &&
    decide (s.regs.FeatureImpl[232] = false))))))) &&
    (((((decide (s.regs.FeatureImpl[138] = true) &&
    decide (s.regs.FeatureImpl[40] = true)) &&
    (decide (s.regs.FeatureImpl[41] = true) &&
    (decide (s.regs.FeatureImpl[76] = true) &&
    decide (s.regs.FeatureImpl[77] = true)))) &&
    ((decide (s.regs.FeatureImpl[78] = true) &&
    decide (s.regs.FeatureImpl[79] = true)) &&
    (decide (s.regs.FeatureImpl[233] = false) &&
    (decide (s.regs.FeatureImpl[234] = false) &&
    decide (s.regs.FeatureImpl[235] = false))))) &&
    (((decide (s.regs.FeatureImpl[236] = false) &&
    decide (s.regs.FeatureImpl[81] = true)) &&
    (decide (s.regs.FeatureImpl[221] = true) &&
    (decide (s.regs.FeatureImpl[222] = true) &&
    decide (s.regs.FeatureImpl[223] = true)))) &&
    ((decide (s.regs.FeatureImpl[224] = true) &&
    (decide (s.regs.FeatureImpl[225] = true) &&
    decide (s.regs.FeatureImpl[226] = true))) &&
    (decide (s.regs.FeatureImpl[227] = false) &&
    (decide (s.regs.FeatureImpl[165] = true) &&
    decide (s.regs.bank_Int .NUM_BREAKPOINTS = 6)))))) &&
    ((((decide (s.regs.bank_Int .NUM_WATCHPOINTS = 4) &&
    decide (s.regs.bank_Int .__num_ctx_breakpoints = 2)) &&
    (decide (_get_EDSCR_Type_STATUS (s.regs.bank_BitVec_32 ._EDSCR) = 0b000010#6) &&
    (decide (s.regs.bank_Bool .SPESampleInFlight = false) &&
    decide (s.regs.PSTATE.EL = 0#2)))) &&
    ((decide (s.regs.PSTATE.nRW = 0#1) &&
    decide (s.regs.PSTATE.IL = 0#1)) &&
    (decide (_get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1) &&
    (decide (_get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1) &&
    decide (_get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1))))) &&
    (((decide (_get_SCR_EL3_Type_NSE (s.regs.bank_BitVec_64 .SCR_EL3) = 0#1) &&
    decide (_get_MDSCR_EL1_Type_SS (s.regs.bank_BitVec_64 .MDSCR_EL1) = 0#1)) &&
    (decide (s.regs.PSTATE.SS = 0#1) &&
    (decide (_get_EDESR_Type_OSUC (s.regs.bank_BitVec_32 .EDESR) = 0#1) &&
    decide (_get_PMBLIMITR_EL1_Type_E (s.regs.bank_BitVec_64 .PMBLIMITR_EL1) = 0#1)))) &&
    ((decide (_get_SCR_EL3_Type_RW (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1) &&
    (decide (_get_SCR_EL3_Type_EEL2 (s.regs.bank_BitVec_64 .SCR_EL3) = 0#1) &&
    decide (_get_TCR_EL2_Type_TBI0 (s.regs.bank_BitVec_64 .TCR_EL2) = 1#1))) &&
    (decide (_get_TCR_EL2_Type_TBID0 (s.regs.bank_BitVec_64 .TCR_EL2) = 0#1) &&
    (decide (_get_MDCR_EL3_Type_NSPB (s.regs.bank_BitVec_64 .MDCR_EL3) = 0b11#2) &&
    decide (_get_MDCR_EL3_Type_NSPBE (s.regs.bank_BitVec_64 .MDCR_EL3) = 0#1))))))))

theorem base_of_check (s : NativeState) (checked : check s = true) : BranchMTE2.Base s := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨⟨⟨⟨⟨⟨p0,p1⟩,⟨p2,⟨p3,p4⟩⟩⟩,⟨⟨p5,p6⟩,⟨p7,⟨p8,p9⟩⟩⟩⟩,⟨⟨⟨p10,p11⟩,⟨p12,⟨p13,p14⟩⟩⟩,⟨⟨p15,⟨p16,p17⟩⟩,⟨p18,⟨p19,p20⟩⟩⟩⟩⟩,⟨⟨⟨⟨p21,p22⟩,⟨p23,⟨p24,p25⟩⟩⟩,⟨⟨p26,p27⟩,⟨p28,⟨p29,p30⟩⟩⟩⟩,⟨⟨⟨p31,p32⟩,⟨p33,⟨p34,p35⟩⟩⟩,⟨⟨p36,⟨p37,p38⟩⟩,⟨p39,⟨p40,p41⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨p42,p43⟩,⟨p44,⟨p45,p46⟩⟩⟩,⟨⟨p47,p48⟩,⟨p49,⟨p50,p51⟩⟩⟩⟩,⟨⟨⟨p52,p53⟩,⟨p54,⟨p55,p56⟩⟩⟩,⟨⟨p57,⟨p58,p59⟩⟩,⟨p60,⟨p61,p62⟩⟩⟩⟩⟩,⟨⟨⟨⟨p63,p64⟩,⟨p65,⟨p66,p67⟩⟩⟩,⟨⟨p68,p69⟩,⟨p70,⟨p71,p72⟩⟩⟩⟩,⟨⟨⟨p73,p74⟩,⟨p75,⟨p76,p77⟩⟩⟩,⟨⟨p78,⟨p79,p80⟩⟩,⟨p81,⟨p82,p83⟩⟩⟩⟩⟩⟩⟩ := checked
  exact {
    hFeature_AA32EL0 := by simpa using p0
    hFeature_AA32EL1 := by simpa using p1
    hFeature_AA32EL2 := by simpa using p2
    hFeature_AA32EL3 := by simpa using p3
    hFeature_AA64EL0 := by simpa using p4
    hFeature_AA64EL1 := by simpa using p5
    hFeature_AA64EL2 := by simpa using p6
    hFeature_AA64EL3 := by simpa using p7
    hFeature_AES := by simpa using p8
    hFeature_AFP := by simpa using p9
    hFeature_AdvSIMD := by simpa using p10
    hFeature_BF16 := by simpa using p11
    hFeature_BRBE := by simpa using p12
    hFeature_BTI := by simpa using p13
    hFeature_CRC32 := by simpa using p14
    hFeature_DGH := by simpa using p15
    hFeature_DIT := by simpa using p16
    hFeature_DPB := by simpa using p17
    hFeature_DPB2 := by simpa using p18
    hFeature_Debugv8p9 := by simpa using p19
    hFeature_DotProd := by simpa using p20
    hFeature_ECV := by simpa using p21
    hFeature_FCMA := by simpa using p22
    hFeature_FHM := by simpa using p23
    hFeature_FP := by simpa using p24
    hFeature_FP16 := by simpa using p25
    hFeature_FRINTTS := by simpa using p26
    hFeature_FlagM := by simpa using p27
    hFeature_FlagM2 := by simpa using p28
    hFeature_I8MM := by simpa using p29
    hFeature_JSCVT := by simpa using p30
    hFeature_LRCPC := by simpa using p31
    hFeature_LRCPC2 := by simpa using p32
    hFeature_LSE := by simpa using p33
    hFeature_LSE2 := by simpa using p34
    hFeature_MOPS := by simpa using p35
    hFeature_MTE := by simpa using p36
    hFeature_PACIMP := by simpa using p37
    hFeature_PFAR := by simpa using p38
    hFeature_PMULL := by simpa using p39
    hFeature_RDM := by simpa using p40
    hFeature_RME := by simpa using p41
    hFeature_SB := by simpa using p42
    hFeature_SHA1 := by simpa using p43
    hFeature_SHA256 := by simpa using p44
    hFeature_SHA3 := by simpa using p45
    hFeature_SHA512 := by simpa using p46
    hFeature_SM3 := by simpa using p47
    hFeature_SM4 := by simpa using p48
    hFeature_SME := by simpa using p49
    hFeature_SME_F64F64 := by simpa using p50
    hFeature_SME_FA64 := by simpa using p51
    hFeature_SME_I16I64 := by simpa using p52
    hFeature_SVE := by simpa using p53
    hFeature_SVE2 := by simpa using p54
    hFeature_SVE_AES := by simpa using p55
    hFeature_SVE_BitPerm := by simpa using p56
    hFeature_SVE_PMULL128 := by simpa using p57
    hFeature_SVE_SHA3 := by simpa using p58
    hFeature_SVE_SM4 := by simpa using p59
    hFeature_TME := by simpa using p60
    hFeature_WFxT := by simpa using p61
    hDebugBP := by simpa using p62
    hDebugWP := by simpa using p63
    hDebugCTX := by simpa using p64
    hEDSCR_STATUS := by simpa using p65
    hSPE := by simpa using p66
    hEL := by simpa using p67
    hnRW := by simpa using p68
    hIL := by simpa using p69
    hE2H := by simpa using p70
    hTGE := by simpa using p71
    hSCR_NS := by simpa using p72
    hSCR_NSE := by simpa using p73
    hMDSCR_SS := by simpa using p74
    hPSTATE_SS := by simpa using p75
    hOSUC := by simpa using p76
    hPMB_E := by simpa using p77
    hSCR_RW := by simpa using p78
    hSCR_EEL2 := by simpa using p79
    hTBI0 := by simpa using p80
    hTBID0 := by simpa using p81
    hNSPB := by simpa using p82
    hNSPBE := by simpa using p83
  }

theorem pins_of_check (s : NativeState) (features : EntryFeatures s.regs)
    (checked : check s = true) (extra : EntryControls.checkBranchExtras s = true) : BranchMTE2.Pins s :=
  ⟨base_of_check s checked,features.vhe,of_decide_eq_true extra⟩

#print axioms check
#print axioms base_of_check
#print axioms pins_of_check
end TranslateSpan.BranchEntryMTE2
