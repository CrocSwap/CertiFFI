import JointEL10.Profile
import GetHostUpper.Facts
import GetHostLower.Facts
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
set_option maxRecDepth 1000000
namespace ArmCert.Eval.JointSAT.EL20
open S1Normality

/-- Public Get, EL2&0 regime: the undefined initial draw, then the EL20 helper. -/
theorem get_eq (ss : SecurityState) (va : BitVec 64) :
    AArch64_GetS1TTWParams .Regime_EL20 ss va =
      (do let _ ← GetGuestFields.Dispatch.initialDraw
          AArch64_S1TTWParamsEL20 ss (AArch64_GetVARange va)) := by
  simp only [AArch64_GetS1TTWParams, GetGuestFields.Dispatch.initialDraw,
    GetGuestReads.unknown_function_eq, GetGuestReads.occurrence_function_eq]

/-- GB10 VHE host TCR (C34: proc.S composition in the TCR_EL1 layout): T0SZ=T1SZ=16,
 4K/4K, WBWA, inner, A1, AS, IPS=5, TBI0=TBI1=1, HA=HD=1, TBID1, NFD1,
    E0PD1, TCMA1; E0PD0=NFD0=EPD0=DS=0. Low 52 bits equal the G3 snapshot word. -/
def tcr : BitVec 64 := 0x055001f5b5503510#64

/-- Register facts consumed by the host Get components. -/
structure Host (s : State) : Prop where
  el3A64 : s.regs.FeatureImpl[7] = true
  noEL3A32 : s.regs.FeatureImpl[3] = false
  noRME : s.regs.FeatureImpl[232] = false
  a64 : s.regs.PSTATE.nRW = 0#1
  tcr : s.regs.bank_BitVec_64 .TCR_EL2 = tcr
  e2h : _get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1
  mair : s.regs.bank_BitVec_64 .MAIR_EL2 = 0x000000040044ffff#64
  tcr2 : s.regs.FeatureImpl[178] = true → s.regs.bank_BitVec_64 .TCR2_EL2 = 0#64

theorem Host.of_regs {s t : State} (h : Host s) (hr : t.regs = s.regs) : Host t := by
  rcases h with ⟨a, b, c, d, e, f, g, i⟩
  exact ⟨by rw [hr]; exact a, by rw [hr]; exact b, by rw [hr]; exact c, by rw [hr]; exact d,
    by rw [hr]; exact e, by rw [hr]; exact f, by rw [hr]; exact g, by rw [hr]; exact i⟩

def Active (wp : S1TTWParams) : Prop :=
  wp.tgx = .TGx_4KB ∧ wp.d128 = 0#1 ∧ wp.aie = 0#1 ∧ wp.ds = 0#1 ∧
    wp.mair = 0x000000040044ffff#64 ∧ wp.txsz = 16#6 ∧ wp.ps = 5#3

theorem range (vr : VARange) (s : State) (h : Host s) :
    ∃ wp t, AArch64_S1TTWParamsEL20 .SS_NonSecure vr s = .ok wp t ∧ Frame s t ∧ Active wp := by
  have hz : ∀ f : BitVec 64 → BitVec 1, f 0#64 = 0#1 → s.regs.FeatureImpl[178] = true →
      f (s.regs.bank_BitVec_64 .TCR2_EL2) = 0#1 := by
    intro f hf h178; rw [h.tcr2 h178]; exact hf
  cases vr with
  | VARange_UPPER =>
    rcases S1ParamsHostUpperFacts.total tcr (s.regs.bank_BitVec_64 .TCR2_EL2)
      (s.regs.bank_BitVec_64 .HCR_EL2) (s.regs.bank_BitVec_64 .SCTLR_EL2)
      (s.regs.bank_BitVec_64 .SCTLR2_EL2) (s.regs.bank_BitVec_64 .SCR_EL3)
      (s.regs.bank_BitVec_64 .MAIR2_EL2) (s.regs.bank_BitVec_64 .PIR_EL2)
      (s.regs.bank_BitVec_64 .PIRE0_EL2) (s.regs.bank_BitVec_128 ._TTBR0_EL2)
      (s.regs.bank_BitVec_128 .TTBR1_EL2) s h.el3A64 h.noEL3A32 h.noRME h.a64 h.tcr
      rfl rfl rfl rfl rfl h.mair rfl rfl rfl rfl rfl (by decide) h.e2h
      (hz _ (by decide)) (hz _ (by decide)) (hz _ (by decide)) (by decide) with
      ⟨wp, t, hr, hf, a, b, c, _, d, e, f, g⟩
    exact ⟨wp, t, hr, hf, a, b, c, d, e, by rw [f]; decide, by rw [g]; decide⟩
  | VARange_LOWER =>
    rcases S1ParamsHostLowerFacts.total tcr (s.regs.bank_BitVec_64 .TCR2_EL2)
      (s.regs.bank_BitVec_64 .HCR_EL2) (s.regs.bank_BitVec_64 .SCTLR_EL2)
      (s.regs.bank_BitVec_64 .SCTLR2_EL2) (s.regs.bank_BitVec_64 .SCR_EL3)
      (s.regs.bank_BitVec_64 .MAIR2_EL2) (s.regs.bank_BitVec_64 .PIR_EL2)
      (s.regs.bank_BitVec_64 .PIRE0_EL2) (s.regs.bank_BitVec_128 ._TTBR0_EL2)
      (s.regs.bank_BitVec_128 .TTBR1_EL2) s h.el3A64 h.noEL3A32 h.noRME h.a64 h.tcr
      rfl rfl rfl rfl rfl h.mair rfl rfl rfl rfl rfl (by decide) h.e2h
      (hz _ (by decide)) (hz _ (by decide)) (hz _ (by decide)) (by decide) with
      ⟨wp, t, hr, hf, a, b, c, _, d, e, f, g⟩
    exact ⟨wp, t, hr, hf, a, b, c, d, e, by rw [f]; decide, by rw [g]; decide⟩

/-- Actual public Get for EL2&0, both VA ranges, under the host register facts. -/
theorem get (va : BitVec 64) (s : State) (h : Host s) :
    ∃ wp t, AArch64_GetS1TTWParams .Regime_EL20 .SS_NonSecure va s = .ok wp t ∧
      Frame s t ∧ Active wp := by
  rw [get_eq]
  rcases GetGuestFields.Dispatch.prefix_normal s with ⟨ig, t, hp, hf⟩
  rcases range (AArch64_GetVARange va) t (h.of_regs hf.1) with ⟨wp, u, hr, hfu, ha⟩
  refine ⟨wp, u, ?_, ⟨hfu.1.trans hf.1, hfu.2.1.trans hf.2.1, hfu.2.2.trans hf.2.2⟩, ha⟩
  simp only [Bind.bind, EStateM.bind, hp, hr]

#print axioms get_eq
#print axioms range
#print axioms get
end ArmCert.Eval.JointSAT.EL20
