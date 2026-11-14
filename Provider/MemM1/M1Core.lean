import MemM1.Wrapper
import MemM1.Callees
import MemM1.Debug
import MemM1.S1TG
import MemM1.Bits
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
namespace MemM1.Witness
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality

/-- Bit-level register facts M1 uses (all on the actual state; no exact words). -/
structure Regs20 (R : Regs) : Prop where
  noRME : R.FeatureImpl[232] = false
  vhe : R.FeatureImpl[54] = true
  aa64el0 : R.FeatureImpl[4] = true
  noPOE : R.FeatureImpl[210] = false
  noGCS : R.FeatureImpl[245] = false
  noPAN : R.FeatureImpl[51] = false
  el0 : R.PSTATE.EL = 0#2
  ns : Sail.BitVec.extractLsb (R.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1
  e2h : Sail.BitVec.extractLsb (R.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 34 34 = 1#1
  tge : Sail.BitVec.extractLsb (R.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 27 27 = 1#1
  m : _get_SCTLR_EL2_Type_M (R.bank_BitVec_64 .SCTLR_EL2) = 1#1
  mde : _get_MDSCR_EL1_Type_MDE (R.bank_BitVec_64 .MDSCR_EL1) = 0#1
  hde : _get_EDSCR_Type_HDE (R.bank_BitVec_32 ._EDSCR) = 0#1
  spe : R.bank_Bool .SPESampleInFlight = false

/-- The EL0 non-secure GPR data access shape M1 covers (read or write). -/
structure Acc0 (acc : AccessDescriptor) : Prop where
  ss : acc.ss = .SS_NonSecure
  el : acc.el = 0#2
  gpr : acc.acctype = .AccessType_GPR
  tag : acc.tagaccess = false
  ls64 : acc.ls64 = false
  tx : acc.transactional = false
  nf : acc.nonfault = false
  ff : acc.firstfault = false

/-- What the walk-parameter fetch and the S1 walk give at VA 0 on states with the
    registers and memory of `s` (supplied by eval M1-a + memory LeafFacts). -/
def WalkOK (acc : AccessDescriptor) (s : State) : Prop :=
  ∀ t : State, t.regs = s.regs → t.mem = s.mem → ∃ wp u,
    AArch64_GetS1TTWParams .Regime_EL20 acc.ss 0#64 t = .ok wp u ∧ Frame t u ∧
    wp.d128 = 0#1 ∧ wp.pie = 0#1 ∧ wp.ds = 0#1 ∧ wp.tgx = .TGx_4KB ∧ wp.txsz = 16#6 ∧
    wp.wxn = 0#1 ∧ wp.e0pd = 0#1 ∧
    ∀ (f' : FaultRecord) (v : State), f'.statuscode = .Fault_None → v.regs = s.regs → v.mem = s.mem →
      ∃ fw wa w d u',
      AArch64_S1Walk f' wp 0#64 .Regime_EL20 acc 64 v = .ok (fw, wa, w, d) u' ∧
      fw.statuscode = .Fault_None ∧ u'.regs = v.regs ∧ u'.mem = v.mem ∧
      d.getLsbD 10 = true ∧ d.getLsbD 51 = false ∧
      w.memattrs.memtype = .MemType_Normal ∧ w.level = 3 ∧ w.contiguous = 0#1 ∧
      w.baseaddress = {paspace := .PAS_NonSecure, address := 0x505000000#56} ∧
      BitVec.setWidth 2 (Sail.BitVec.extractLsb w.permissions.ap 2 1) = 1#2 ∧
      w.permissions.ap_table = 0#2

/-- M1 core: the actual AArch64_TranslateAddress at VA 0. -/
theorem core (acc : AccessDescriptor) (aligned : Bool) (size : Int) (s : State)
    (hR : Regs20 s.regs) (hA : Acc0 acc) (hW : WalkOK acc s) :
    ∃ ad t, AArch64_TranslateAddress 0#64 acc aligned size s = .ok ad t ∧
      ad.fault.statuscode = .Fault_None ∧
      ad.paddress = {paspace := .PAS_NonSecure, address := 0x505000000#56} ∧
      ad.memattrs.memtype = .MemType_Normal ∧ t.regs = s.regs ∧ t.mem = s.mem := by
  have regime : ∀ t : State, t.regs = s.regs →
      ∃ u, TranslationRegime acc.el t = .ok .Regime_EL20 u ∧ Frame t u := by
    intro t ht
    rw [hA.el]
    exact MemM1.Callees.regime_el0 t (by rw [ht]; exact hR.noRME) (by rw [ht]; exact hR.vhe)
      (by rw [ht]; exact hR.aa64el0) (by rw [ht]; exact hR.ns) (by rw [ht]; exact hR.e2h)
      (by rw [ht]; exact hR.tge)
  rcases regime s rfl with ⟨s0, h0, f0⟩
  rcases MemM1.Callees.tsi acc.ss acc 0#64 size s0 with ⟨ti, s1, h1, f1⟩
  have hs1 : s1.regs = s.regs := f1.1.trans f0.1
  have hm1 : s1.mem = s.mem := f1.2.1.trans f0.2.1
  let P : AddressDescriptor → State → Prop := fun ipa u =>
    ipa.paddress = {paspace := .PAS_NonSecure, address := 0x505000000#56} ∧
      ipa.memattrs.memtype = .MemType_Normal ∧ ipa.fault.statuscode = .Fault_None ∧
      u.regs = s.regs ∧ u.mem = s.mem
  have hP : ∀ ad t u, P ad t → Frame t u → P ad u := fun _ _ _ ⟨a1, a2, a3, a4, a5⟩ fu =>
    ⟨a1, a2, a3, fu.1.trans a4, fu.2.1.trans a5⟩
  rcases MemM1.Full.full 0#64 acc aligned { s1 with events := s1.events.push (.translationStart ti) } P hP
      hA.ss (fun t ht => regime t (ht.1.trans hs1))
      (fun f t ht hf => by
        have htr : t.regs = s.regs := ht.1.trans hs1
        have htm : t.mem = s.mem := ht.2.1.trans hm1
        rcases MemM1.S1TG.s1t_g f aligned acc t _ rfl hf hA.el hA.gpr hA.tag hA.ls64 hA.tx hA.nf hA.ff
            (by rw [htr]; exact hR.noPOE) (by rw [htr]; exact hR.noGCS) (by rw [htr]; exact hR.noPAN)
            (MemM1.Bits.en acc.acctype t (by rw [htr]; exact hR.m))
            (fun t' ht' => by
              rcases hW t' (ht'.1.trans htr) (ht'.2.1.trans htm) with
                ⟨wp, u, hg, fu, a1, a2, a3, a4, a5, a6, a7, hwk⟩
              exact ⟨wp, u, hg, fu, a1, a2, a3, a4, a5, a6, a7, fun f' v hf' hv =>
                hwk f' v hf' (hv.1.trans htr) (hv.2.1.trans htm)⟩) with
          ⟨fr, ipa, u, h, hfr, hpa, hmt, hif, fur, fum⟩
        exact ⟨fr, ipa, u, h, hfr, hpa, hmt, hif, fur.trans htr, fum.trans htm⟩) with
    ⟨ad, t, hfull, hpa, hmt, hadf, htr, htm⟩
  rcases MemM1.Debug.no_fault 0#64 acc size t (by rw [htr]; exact hR.el0) (by rw [htr]; exact hR.noRME)
      (by rw [htr]; exact hR.aa64el0) (by rw [htr]; exact hR.ns)
      (by rw [htr]; exact MemM1.Bits.mde _ hR.mde) (by rw [htr]; exact MemM1.Bits.hde _ hR.hde) with
    ⟨df, t2, hdbg, hdf, f2⟩
  have ht2 : t2.regs = s.regs := f2.1.trans htr
  have hIF : acc.acctype ≠ .AccessType_IFETCH := by rw [hA.gpr]; intro h; cases h
  rcases MemM1.Wrapper.translate 0#64 acc aligned size s .Regime_EL20 s0 ti s1 ad t df t2
      (MemM1.Bits.spe _ hR.spe) h0 h1 hfull hadf hIF hdbg hdf
      (MemM1.Callees.rme t2 (by rw [ht2]; exact hR.noRME))
      (by rw [ht2]; exact MemM1.Bits.spe _ hR.spe) with ⟨t3, h3, hr3, hm3⟩
  exact ⟨_, t3, h3, hdf, hpa, hmt, hr3.trans ht2, hm3.trans (f2.2.1.trans htm)⟩

#print axioms core
end MemM1.Witness
