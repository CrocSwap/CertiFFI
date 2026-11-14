import Walk.S1ParamsUnknown
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
set_option linter.unusedVariables false
namespace S1ParamsHostLower
/- Named source-register premises. Unimplemented TCR2 is not constrained:
   the zero-field premises apply only when FEAT_TCRX is implemented. This is
   a source-parameter bridge, not yet a joint hardware/profile SAT theorem. -/
set_option maxHeartbeats 1000000 in
drive_spec native, complete :
  fun (tcr tcr2 hcr sctlr sctlr2 scr mair2 pir pire0 : BitVec 64)
      (ttbr0 ttbr1 : BitVec 128) (s : SequentialState Regs oracleChoiceSource)
      (hEL3A64 : s.regs.FeatureImpl[7] = true)
      (hNoEL3A32 : s.regs.FeatureImpl[3] = false)
      (hNoRME : s.regs.FeatureImpl[232] = false)
      (hA64 : s.regs.PSTATE.nRW = 0#1)
      (hTCR : s.regs.bank_BitVec_64 .TCR_EL2 = tcr)
      (hTCR2 : s.regs.bank_BitVec_64 .TCR2_EL2 = tcr2)
      (hHCR : s.regs.bank_BitVec_64 .HCR_EL2 = hcr)
      (hSCTLR : s.regs.bank_BitVec_64 .SCTLR_EL2 = sctlr)
      (hSCTLR2 : s.regs.bank_BitVec_64 .SCTLR2_EL2 = sctlr2)
      (hSCR : s.regs.bank_BitVec_64 .SCR_EL3 = scr)
      (hMAIR : s.regs.bank_BitVec_64 .MAIR_EL2 = 0x000000040044ffff#64)
      (hMAIR2 : s.regs.bank_BitVec_64 .MAIR2_EL2 = mair2)
      (hPIR : s.regs.bank_BitVec_64 .PIR_EL2 = pir)
      (hPIRE0 : s.regs.bank_BitVec_64 .PIRE0_EL2 = pire0)
      (hTTBR0 : s.regs.bank_BitVec_128 ._TTBR0_EL2 = ttbr0)
      (hTTBR1 : s.regs.bank_BitVec_128 .TTBR1_EL2 = ttbr1)
      (hTG : _get_TCR_EL2_Type_TG0 tcr = 0#2)
      (hE2H : _get_HCR_EL2_Type_E2H hcr = 1#1)
      (hD128 : s.regs.FeatureImpl[178] = true → _get_TCR2_EL2_Type_D128 tcr2 = 0#1)
      (hAIE : s.regs.FeatureImpl[178] = true → _get_TCR2_EL2_Type_AIE tcr2 = 0#1)
      (hPnCH : s.regs.FeatureImpl[178] = true → _get_TCR2_EL2_Type_PnCH tcr2 = 0#1)
      (hDS : BitVec.slice tcr 59 1 = 0#1) =>
    AArch64_S1TTWParamsEL20 .SS_NonSecure .VARange_LOWER s
attribute [step_summary] complete
#print axioms complete
end S1ParamsHostLower
