import GetHostUpper.Params
import Walk.S1WalkChecks
import Pilot.ObservationSimp
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1ParamsHostUpperFacts
open S1Normality

def Shape (tcr : BitVec 64) (wp : S1TTWParams) : Prop :=
  wp.tgx = .TGx_4KB ∧ wp.d128 = 0#1 ∧ wp.aie = 0#1 ∧ wp.pnch = 0#1 ∧
    wp.ds = 0#1 ∧ wp.mair = 0x000000040044ffff#64 ∧
    wp.txsz = _get_TCR_EL2_Type_T1SZ tcr ∧ wp.ps = _get_TCR_EL2_Type_IPS tcr

def Good (tcr : BitVec 64) (s : State) :
    EStateM.Result (Sail.Error exception) State S1TTWParams → Prop
  | .ok wp t => Frame s t ∧ Shape tcr wp
  | .error _ _ => False

theorem native_good (tcr tcr2 hcr sctlr sctlr2 scr mair2 pir pire0 : BitVec 64)
    (ttbr0 ttbr1 : BitVec 128) (s : State)
    (hD128 : s.regs.FeatureImpl[178] = true → _get_TCR2_EL2_Type_D128 tcr2 = 0#1)
    (hPnCH : s.regs.FeatureImpl[178] = true → _get_TCR2_EL2_Type_PnCH tcr2 = 0#1)
    (hDS : BitVec.slice tcr 59 1 = 0#1) :
    Good tcr s (S1ParamsHostUpper.native tcr tcr2 hcr sctlr sctlr2 scr mair2 pir pire0 ttbr0 ttbr1 s) := by
  observe_simp [Good, Frame, Shape, S1ParamsHostUpper.native, Mk_MAIRType]
  constructor
  · intro h242 h178 hscr hss
    exact hD128 h178
  · intro h218 hbranch h178 hscr hss
    exact hPnCH h178
#print axioms native_good


theorem total (tcr tcr2 hcr sctlr sctlr2 scr mair2 pir pire0 : BitVec 64)
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
      (hTG : _get_TCR_EL2_Type_TG1 tcr = 2#2)
      (hE2H : _get_HCR_EL2_Type_E2H hcr = 1#1)
      (hD128 : s.regs.FeatureImpl[178] = true → _get_TCR2_EL2_Type_D128 tcr2 = 0#1)
      (hAIE : s.regs.FeatureImpl[178] = true → _get_TCR2_EL2_Type_AIE tcr2 = 0#1)
      (hPnCH : s.regs.FeatureImpl[178] = true → _get_TCR2_EL2_Type_PnCH tcr2 = 0#1)
      (hDS : BitVec.slice tcr 59 1 = 0#1) :
    ∃ wp t, AArch64_S1TTWParamsEL20 .SS_NonSecure .VARange_UPPER s = .ok wp t ∧
      Frame s t ∧ Shape tcr wp := by
  have hg := native_good tcr tcr2 hcr sctlr sctlr2 scr mair2 pir pire0 ttbr0 ttbr1 s hD128 hPnCH hDS
  have hr := S1ParamsHostUpper.complete tcr tcr2 hcr sctlr sctlr2 scr mair2 pir pire0 ttbr0 ttbr1 s
    hEL3A64 hNoEL3A32 hNoRME hA64 hTCR hTCR2 hHCR hSCTLR hSCTLR2 hSCR hMAIR hMAIR2 hPIR hPIRE0
    hTTBR0 hTTBR1 hTG hE2H hD128 hAIE hPnCH hDS
  rw [← hr] at hg
  cases he : AArch64_S1TTWParamsEL20 .SS_NonSecure .VARange_UPPER s with
  | error e t => simp only [he, Good] at hg
  | ok wp t => exact ⟨wp, t, rfl, by simpa only [he, Good] using hg⟩
#print axioms total
end S1ParamsHostUpperFacts
