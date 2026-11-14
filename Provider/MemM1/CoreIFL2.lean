import MemM1.S1TIFRWL2
import MemM1.TrIFE
import MemM1.LeafFactsGCW
import MemM1.WalkKE
import MemM1.ConsumerV3
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.CoreIFL2
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.NoFault MemM1.WitnessIF MemM1.WitnessIFE
open S1OuterSetup ArmCert.Eval.JointSAT ArmCert.Eval.M1a ArmCert.Eval.M1a.TWP ArmCert.Eval.M1a.WEv
open ArmCert.Premises.TranslationAgreesV3
open MemM1.WalkKE (walkK readsOK ok_inj)

/-! Level-2 (2 MB block) versions of `TrIFE.WalkOKIFRW` / `TrIFE.coreIFRW` (PA = `VA2.blockOA B va`). -/

/-- `MBV2.WalkOKIFR` plus the walk state's inner/outer write-back attributes. -/
def WalkOKIFRW2 (acc : AccessDescriptor) (s : State) (va : BitVec 64) (B : BitVec 56)
    (R : Array Event → Prop) : Prop :=
  ∀ t : State, t.regs = s.regs → t.mem = s.mem → ∃ wp u,
    AArch64_GetS1TTWParams .Regime_EL20 acc.ss va t = .ok wp u ∧ Frame t u ∧
    wp.d128 = 0#1 ∧ wp.pie = 0#1 ∧ wp.ds = 0#1 ∧ wp.tgx = .TGx_4KB ∧ wp.txsz = 16#6 ∧
    wp.wxn = 0#1 ∧ wp.e0pd = 0#1 ∧
    ∀ (f' : FaultRecord) (v : State), f'.statuscode = .Fault_None → v.regs = s.regs → v.mem = s.mem →
      ∃ fw wa w d u',
      AArch64_S1Walk f' wp va .Regime_EL20 acc 64 v = .ok (fw, wa, w, d) u' ∧
      fw.statuscode = .Fault_None ∧ u'.regs = v.regs ∧ u'.mem = v.mem ∧
      (∃ W, u'.events = v.events ++ W ∧ R W) ∧
      d.getLsbD 10 = true ∧ d.getLsbD 51 = false ∧
      w.memattrs.memtype = .MemType_Normal ∧
      w.memattrs.inner.attrs = MemAttr_WB ∧ w.memattrs.outer.attrs = MemAttr_WB ∧ w.level = 2 ∧
      w.contiguous = 0#1 ∧
      w.baseaddress = {paspace := .PAS_NonSecure, address := B} ∧
      w.permissions.uxn = 0#1 ∧ w.permissions.uxn_table = 0#1 ∧ w.guardedpage = 0#1

theorem walkOKIFRW2_regs {acc : AccessDescriptor} {s u : State} {va : BitVec 64} {B : BitVec 56}
    {R : Array Event → Prop} (h : WalkOKIFRW2 acc s va B R) (hr : u.regs = s.regs) (hm : u.mem = s.mem) :
    WalkOKIFRW2 acc u va B R := by
  unfold WalkOKIFRW2 at h ⊢
  rw [hr, hm]
  exact h

/-- `MBV2.coreIFR` with SCTLR_EL2.I = 1 and write-back walk attributes: the output descriptor is
    inner/outer write-back. -/
theorem coreIFRW2 (va : BitVec 64) (hva : va.toNat < 2^48) (B : BitVec 56)
    (hB : B &&& 0x1fffff#56 = 0#56) (acc : AccessDescriptor) (aligned : Bool) (size : Int) (s : State)
    (R : Array Event → Prop)
    (hR : Witness.Regs20 s.regs) (hA : AccIF acc) (hW : WalkOKIFRW2 acc s va B R)
    (hI : _get_SCTLR_EL2_Type_I (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1) :
    ∃ ti ad t W, AArch64_TranslateAddress va acc aligned size s = .ok ad t ∧
      ad.fault.statuscode = .Fault_None ∧
      ad.paddress = {paspace := .PAS_NonSecure, address := MemM1.VA2.blockOA B va} ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ ad.vaddress = va ∧
      t.regs = MemM1.IF.clrGP s.regs ∧ t.mem = s.mem ∧
      t.events = s.events ++ (#[Event.translationStart ti] ++ W ++ #[Event.translationEnd ad]) ∧
      TSIOK ti acc va size s ∧ R W := by
  have regime : ∀ t : State, t.regs = s.regs →
      ∃ u, TranslationRegime acc.el t = .ok .Regime_EL20 u ∧ Frame t u := by
    intro t ht
    rw [hA.el]
    exact MemM1.Callees.regime_el0 t (by rw [ht]; exact hR.noRME) (by rw [ht]; exact hR.vhe)
      (by rw [ht]; exact hR.aa64el0) (by rw [ht]; exact hR.ns) (by rw [ht]; exact hR.e2h)
      (by rw [ht]; exact hR.tge)
  rcases regime s rfl with ⟨s0, h0, f0⟩
  rcases MemM1.Callees.tsi acc.ss acc va size s0 with ⟨ti, s1, h1, f1⟩
  have hs1 : s1.regs = s.regs := f1.1.trans f0.1
  have hm1 : s1.mem = s.mem := f1.2.1.trans f0.2.1
  have he1 : s1.events = s.events := f1.2.2.trans f0.2.2
  let s1' : State := { s1 with events := s1.events.push (.translationStart ti) }
  let P : AddressDescriptor → State → Prop := fun ipa u =>
    ipa.paddress = {paspace := .PAS_NonSecure, address := MemM1.VA2.blockOA B va} ∧
      ipa.memattrs.memtype = .MemType_Normal ∧ ipa.memattrs.inner.attrs = MemAttr_WB ∧
      ipa.memattrs.outer.attrs = MemAttr_WB ∧ ipa.fault.statuscode = .Fault_None ∧
      u.regs = MemM1.IF.clrGP s.regs ∧ u.mem = s.mem ∧ ∃ W, u.events = s1'.events ++ W ∧ R W
  have hP : ∀ ad t u, P ad t → Frame t u → P ad u := fun _ _ _ ⟨a1, a2, b1, b2, a3, a4, a5, W, a6, a7⟩ fu =>
    ⟨a1, a2, b1, b2, a3, fu.1.trans a4, fu.2.1.trans a5, W, fu.2.2.trans a6, a7⟩
  rcases MemM1.Full.full va acc aligned s1' P hP
      hA.ss (fun t ht => regime t (ht.1.trans hs1))
      (fun f t ht hf => by
        have htr : t.regs = s.regs := ht.1.trans hs1
        have htm : t.mem = s.mem := ht.2.1.trans hm1
        rcases MemM1.S1TIFRWL2.s1t_ifrwl2 R f va hva B hB aligned acc t _ rfl hf hA.el hA.ifetch hA.ss hA.ls64
            hA.tx hA.nf hA.ff (by rw [htr]; exact hR.noPOE) (by rw [htr]; exact hR.noPAN) (by rw [htr]; exact hI)
            (MemM1.Bits.en acc.acctype t (by rw [htr]; exact hR.m))
            (fun t' ht' => by
              rcases hW t' (ht'.1.trans htr) (ht'.2.1.trans htm) with
                ⟨wp, u, hg, fu, a1, a2, a3, a4, a5, a6, a7, hwk⟩
              exact ⟨wp, u, hg, fu, a1, a2, a3, a4, a5, a6, a7, fun f' v hf' hv =>
                hwk f' v hf' (hv.1.trans htr) (hv.2.1.trans htm)⟩) with
          ⟨fr, ipa, u, h, hfr, hpa, hmt, hin, hout, hif, fur, fum, W, fue, hRW⟩
        exact ⟨fr, ipa, u, h, hfr, hpa, hmt, hin, hout, hif, fur.trans (by rw [htr]), fum.trans htm,
          W, fue.trans (by rw [ht.2.2]), hRW⟩) with
    ⟨ad, t, hfull, hpa, hmt, hin, hout, hadf, htr, htm, W, hte, hRW⟩
  rcases MemM1.Debug.no_fault va acc size t (by rw [htr]; exact hR.el0) (by rw [htr]; exact hR.noRME)
      (by rw [htr]; exact hR.aa64el0) (by rw [htr]; exact hR.ns)
      (by rw [htr]; exact MemM1.Bits.mde _ hR.mde) (by rw [htr]; exact MemM1.Bits.hde _ hR.hde) with
    ⟨df, t2, hdbg, hdf, f2⟩
  have h3 := translateIFE va acc aligned size s .Regime_EL20 s0 ti s1 ad t df t2 hA.ifetch h0 h1 hfull hadf
      (MemM1.Callees.rme t (by rw [htr]; exact hR.noRME)) hdbg
  rcases tsi_fields _ _ _ _ _ _ _ _ h1 with ⟨q1, q2, q3, q4, q5⟩
  refine ⟨ti, _, _, W, h3, hdf, hpa, hmt, hin, hout, ?_, f2.1.trans htr, f2.2.1.trans htm, ?_,
    ⟨q1.trans hA.ss, q2, q3, q4, q5, s0, s1, f0, h1⟩, hRW⟩
  · show Sail.BitVec.zeroExtend va 64 = va
    simp [Sail.BitVec.zeroExtend]
  · show (t2.events.push _) = _
    rw [f2.2.2, hte]
    show ((s1.events.push _) ++ W).push _ = _
    rw [he1, ev_shape]

#print axioms walkOKIFRW2_regs
#print axioms coreIFRW2

end MemM1.CoreIFL2
