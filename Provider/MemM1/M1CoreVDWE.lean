import MemM1.M1Core
import MemM1.S1TGVDW
import MemM1.S1TGVDWE
import MemM1.M1CoreVDW
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
namespace MemM1.WitnessVDWE
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality

/-- What the walk-parameter fetch and the S1 walk give at VA `va` on states with the
    registers and memory of `s`: as `Witness.WalkOK`, but at `va`, with leaf base `B`,
    and descriptor bit 7 (AP[2]) = 0 in place of DBM (bit 51) = 0, and inner/outer write-back
    walk-state attributes; plus: the walk appends some `W` with `R W`. -/
def WalkOKVDWR (acc : AccessDescriptor) (s : State) (va : BitVec 64) (B : BitVec 56)
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
      d.getLsbD 10 = true ∧ d.getLsbD 7 = false ∧
      w.memattrs.memtype = .MemType_Normal ∧
      w.memattrs.inner.attrs = MemAttr_WB ∧ w.memattrs.outer.attrs = MemAttr_WB ∧ w.level = 3 ∧ w.contiguous = 0#1 ∧
      w.baseaddress = {paspace := .PAS_NonSecure, address := B} ∧
      BitVec.setWidth 2 (Sail.BitVec.extractLsb w.permissions.ap 2 1) = 1#2 ∧
      w.permissions.ap_table = 0#2

/-- `Wrapper.translate` with the final state exposed: a data TranslateAddress returns
    `{ad with fault := df, vaddress := va}` and appends exactly the translation-end event. -/
theorem translateE (va : BitVec 64) (acc : AccessDescriptor) (aligned : Bool) (size : Int) (s : State)
    (R : Regime) (s0 : State) (tsi : TranslationStartInfo) (s1 : State) (ad : AddressDescriptor) (t : State)
    (df : FaultRecord) (t2 : State)
    (hspe : Register.SPESampleInFlight.get s.regs = false)
    (hreg : TranslationRegime acc.el s = .ok R s0)
    (htsi : AArch64_GetTranslationStartInfo R acc.ss acc va size s0 = .ok tsi s1)
    (hfull : AArch64_FullTranslate va acc aligned
      { s1 with events := s1.events.push (.translationStart tsi) } = .ok ad t)
    (hnf : ad.fault.statuscode = .Fault_None)
    (hnotif : acc.acctype ≠ .AccessType_IFETCH)
    (hdbg : AArch64_CheckDebug va acc size t = .ok df t2)
    (hdf : df.statuscode = .Fault_None)
    (hrme : HaveRME () t2 = .ok false t2)
    (hspe2 : Register.SPESampleInFlight.get t2.regs = false) :
    AArch64_TranslateAddress va acc aligned size s =
        .ok { ad with fault := df, vaddress := Sail.BitVec.zeroExtend va 64 }
          { t2 with events := t2.events.push (Event.translationEnd
            { ad with fault := df, vaddress := Sail.BitVec.zeroExtend va 64 }) } := by
  have hnn : (Fault.Fault_None != Fault.Fault_None) = false := rfl
  have hacc : (acc.acctype != AccessType.AccessType_IFETCH) = true := by
    cases h : acc.acctype <;> first | rfl | exact absurd h hnotif
  have hacc2 : (acc.acctype == AccessType.AccessType_IFETCH) = false := by
    cases h : acc.acctype <;> first | rfl | exact absurd h hnotif
  have hdfn : (df.statuscode != Fault.Fault_None) = false := by rw [hdf]; rfl
  unfold AArch64_TranslateAddress
  simp only [Bind.bind, EStateM.bind, readReg, PreSail.readReg_apply, hspe, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte, Pure.pure, EStateM.pure, start_translation,
    ArmFull.ConcurrencyInterfaceV1.sail_translation_start, PreSail.sail_translation_start, PreSail.logEvent,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  simp only [hreg, htsi]
  simp only [hfull, IsFault, hnf, hnn, Bool.not_false, Bool.true_and, hacc, ↓reduceIte, EStateM.bind, EStateM.pure,
    hdbg, hrme, Bool.false_and, Bool.false_eq_true, hdfn, hspe2, hacc2, Bool.false_or, end_translation,
    ArmFull.ConcurrencyInterfaceV1.sail_translation_end, PreSail.sail_translation_end, PreSail.logEvent,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
#print axioms translateE

theorem ev_shape (a W : Array Event) (x y : Event) :
    (a.push x ++ W).push y = a ++ #[x] ++ W ++ #[y] := by
  rw [Array.push_eq_append, Array.push_eq_append]

/-- `WitnessVD.coreVD` strengthened for E17S: with SCTLR_EL2.C = 1 the output descriptor carries the
    walk's inner/outer write-back attributes, and TranslateAddress returns `vaddress = va`. -/
theorem coreVDWE (R : Array Event → Prop) (va : BitVec 64) (hva : va.toNat < 2^48) (B : BitVec 56)
    (hB : B &&& 0xfff#56 = 0#56) (acc : AccessDescriptor) (aligned : Bool) (size : Int) (s : State)
    (hR : Witness.Regs20 s.regs) (hA : Witness.Acc0 acc) (hW : WalkOKVDWR acc s va B R)
    (hC : _get_SCTLR_EL2_Type_C (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1) :
    ∃ ad t, AArch64_TranslateAddress va acc aligned size s = .ok ad t ∧
      ad.fault.statuscode = .Fault_None ∧
      ad.paddress = {paspace := .PAS_NonSecure, address := MemM1.VA.pageOA B va} ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ ad.vaddress = va ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧
      ∃ ti W, t.events = s.events ++ #[Event.translationStart ti] ++ W ++ #[Event.translationEnd ad] ∧
        R W := by
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
    ipa.paddress = {paspace := .PAS_NonSecure, address := MemM1.VA.pageOA B va} ∧
      ipa.memattrs.memtype = .MemType_Normal ∧ ipa.memattrs.inner.attrs = MemAttr_WB ∧
      ipa.memattrs.outer.attrs = MemAttr_WB ∧ ipa.fault.statuscode = .Fault_None ∧
      u.regs = s.regs ∧ u.mem = s.mem ∧ ∃ W, u.events = s1'.events ++ W ∧ R W
  have hP : ∀ ad t u, P ad t → Frame t u → P ad u := fun _ _ _ ⟨a1, a2, b1, b2, a3, a4, a5, W, a6, a7⟩ fu =>
    ⟨a1, a2, b1, b2, a3, fu.1.trans a4, fu.2.1.trans a5, W, fu.2.2.trans a6, a7⟩
  rcases MemM1.Full.full va acc aligned s1' P hP
      hA.ss (fun t ht => regime t (ht.1.trans hs1))
      (fun f t ht hf => by
        have htr : t.regs = s.regs := ht.1.trans hs1
        have htm : t.mem = s.mem := ht.2.1.trans hm1
        rcases MemM1.S1TGVDWE.s1t_gvdwe R f va hva B hB aligned acc t _ rfl hf hA.el hA.gpr hA.tag hA.ls64 hA.tx hA.nf hA.ff
            (by rw [htr]; exact hR.noPOE) (by rw [htr]; exact hR.noGCS) (by rw [htr]; exact hR.noPAN) (by rw [htr]; exact hC)
            (MemM1.Bits.en acc.acctype t (by rw [htr]; exact hR.m))
            (fun t' ht' => by
              rcases hW t' (ht'.1.trans htr) (ht'.2.1.trans htm) with
                ⟨wp, u, hg, fu, a1, a2, a3, a4, a5, a6, a7, hwk⟩
              exact ⟨wp, u, hg, fu, a1, a2, a3, a4, a5, a6, a7, fun f' v hf' hv =>
                hwk f' v hf' (hv.1.trans htr) (hv.2.1.trans htm)⟩) with
          ⟨fr, ipa, u, h, hfr, hpa, hmt, hin, hout, hif, fur, fum, W, fue, hRW⟩
        exact ⟨fr, ipa, u, h, hfr, hpa, hmt, hin, hout, hif, fur.trans htr, fum.trans htm, W,
          fue.trans (by rw [ht.2.2]), hRW⟩) with
    ⟨ad, t, hfull, hpa, hmt, hin, hout, hadf, htr, htm, W, hte, hRW⟩
  rcases MemM1.Debug.no_fault va acc size t (by rw [htr]; exact hR.el0) (by rw [htr]; exact hR.noRME)
      (by rw [htr]; exact hR.aa64el0) (by rw [htr]; exact hR.ns)
      (by rw [htr]; exact MemM1.Bits.mde _ hR.mde) (by rw [htr]; exact MemM1.Bits.hde _ hR.hde) with
    ⟨df, t2, hdbg, hdf, f2⟩
  have ht2 : t2.regs = s.regs := f2.1.trans htr
  have hIF : acc.acctype ≠ .AccessType_IFETCH := by rw [hA.gpr]; intro h; cases h
  have h3 := translateE va acc aligned size s .Regime_EL20 s0 ti s1 ad t df t2
      (MemM1.Bits.spe _ hR.spe) h0 h1 hfull hadf hIF hdbg hdf
      (MemM1.Callees.rme t2 (by rw [ht2]; exact hR.noRME))
      (by rw [ht2]; exact MemM1.Bits.spe _ hR.spe)
  refine ⟨_, _, h3, hdf, hpa, hmt, hin, hout, MemM1.WitnessVDW.zext va, ht2, f2.2.1.trans htm, ti, W, ?_, hRW⟩
  show (t2.events.push _) = _
  rw [f2.2.2, hte]
  show ((s1.events.push _) ++ W).push _ = _
  rw [he1, ev_shape]

#print axioms coreVDWE
end MemM1.WitnessVDWE
