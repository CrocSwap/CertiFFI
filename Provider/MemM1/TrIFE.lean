import MemM1.S1TIFRW
import MemM1.LeafFactsGCW
import MemM1.WalkKE
import MemM1.ConsumerV3
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.TrIFE
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.NoFault MemM1.WitnessIF MemM1.WitnessIFE
open S1OuterSetup ArmCert.Eval.JointSAT ArmCert.Eval.M1a ArmCert.Eval.M1a.TWP ArmCert.Eval.M1a.WEv
open ArmCert.Premises.TranslationAgreesV3
open MemM1.WalkKE (walkK readsOK ok_inj)

/-! IFETCH analogue of `WalkKE.tr_dataE`: code pages, SCTLR_EL2.I = 1, inner/outer WB. -/

/-- `MBV2.WalkOKIFR` plus the walk state's inner/outer write-back attributes. -/
def WalkOKIFRW (acc : AccessDescriptor) (s : State) (va : BitVec 64) (B : BitVec 56)
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
      w.memattrs.inner.attrs = MemAttr_WB ∧ w.memattrs.outer.attrs = MemAttr_WB ∧ w.level = 3 ∧
      w.contiguous = 0#1 ∧
      w.baseaddress = {paspace := .PAS_NonSecure, address := B} ∧
      w.permissions.uxn = 0#1 ∧ w.permissions.uxn_table = 0#1 ∧ w.guardedpage = 0#1

theorem walkOKIFRW_regs {acc : AccessDescriptor} {s u : State} {va : BitVec 64} {B : BitVec 56}
    {R : Array Event → Prop} (h : WalkOKIFRW acc s va B R) (hr : u.regs = s.regs) (hm : u.mem = s.mem) :
    WalkOKIFRW acc u va B R := by
  unfold WalkOKIFRW at h ⊢
  rw [hr, hm]
  exact h

/-- `MBV2.coreIFR` with SCTLR_EL2.I = 1 and write-back walk attributes: the output descriptor is
    inner/outer write-back. -/
theorem coreIFRW (va : BitVec 64) (hva : va.toNat < 2^48) (B : BitVec 56)
    (hB : B &&& 0xfff#56 = 0#56) (acc : AccessDescriptor) (aligned : Bool) (size : Int) (s : State)
    (R : Array Event → Prop)
    (hR : Witness.Regs20 s.regs) (hA : AccIF acc) (hW : WalkOKIFRW acc s va B R)
    (hI : _get_SCTLR_EL2_Type_I (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1) :
    ∃ ti ad t W, AArch64_TranslateAddress va acc aligned size s = .ok ad t ∧
      ad.fault.statuscode = .Fault_None ∧
      ad.paddress = {paspace := .PAS_NonSecure, address := MemM1.VA.pageOA B va} ∧
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
    ipa.paddress = {paspace := .PAS_NonSecure, address := MemM1.VA.pageOA B va} ∧
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
        rcases MemM1.S1TIFRW.s1t_ifrw R f va hva B hB aligned acc t _ rfl hf hA.el hA.ifetch hA.ss hA.ls64
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

#print axioms coreIFRW

/-- **Bridge (code pages)**: eval's `WalkFactE` + code-leaf bits + an EL0 NS IFETCH access ⇒ the
    event-tracking, write-back walk hypothesis with `TTWReadsOK (walkK s.regs s.mem) va`. -/
theorem walkOKIFRW_of (s : State) (va D : BitVec 64) (hWE : WalkFactE s va D)
    (hD : MemM1.WalkFactV.LeafBitsC D) (acc : AccessDescriptor) (hA : AccIF acc) :
    WalkOKIFRW acc s va (MemM1.LeafFactsG.leafBase D) (TTWReadsOK (walkK s.regs s.mem) va) := by
  intro t htr htm
  let f0 : FaultRecord := { (default : FaultRecord) with statuscode := .Fault_None }
  rcases hWE t htr htm f0 acc rfl hA.ss with ⟨wp, u, hg, hfr, hF, hAct, _⟩
  rcases hF with ⟨hee, hwxn, _, _, hpie, _, he0pd, _⟩
  rcases hAct with ⟨htg, hd128, haie, hds, hmair, htx, _⟩
  refine ⟨wp, u, hg, hfr, hd128, hpie, hds, htg, htx, hwxn, he0pd, ?_⟩
  intro f' v hf' hvr hvm
  rcases hWE t htr htm f' acc hf' hA.ss with ⟨wp', u', hg', _, _, _, Hv⟩
  obtain rfl : wp' = wp := (ok_inj (hg'.symm.trans hg)).1
  rcases Hv v (hvr.trans htr.symm) (hvm.trans htm.symm) with
    ⟨c, ⟨fw, wa, w, d⟩, x, hcwp, hcacc, _, _, hwalk, ⟨hwr, hwm, hd, hfw, _, cur, m, hcl, hcpas, _, hcuxt, _, hlv⟩,
      W, hWev, hWs, hRA⟩
  subst hcwp
  have hdec : S2FetchFrame.decoded c.wp.ee D = D := by
    unfold S2FetchFrame.decoded; rw [hee]; rfl
  rw [hdec] at hd hlv
  rcases MemM1.LeafFactsGCW.leafGCW_x cur m c.wp D w v.regs hcl hcpas hmair hd128 htg hpie hds haie hcuxt
      hD.idx hD.dbm' hD.cont hD.uxn hD.gp hlv with ⟨hmt, hin, hout, hl, hc, hb, hux, huxt, hgp⟩
  have hdD : d = D := hd
  rw [hvm] at hRA
  refine ⟨fw, wa, w, d, x, hwalk, hfw, hwr, hwm, ⟨W, hWev, readsOK _ hee s.regs s.mem va W hRA⟩,
    ?_, ?_, hmt, hin, hout, hl, hc, hb, hux, huxt, hgp⟩
  · rw [hdD]; exact hD.af
  · rw [hdD]; exact hD.dbm

/-- **The AgreesV3 conjuncts for one instruction fetch on a code page**, on any state `u` with
    `s`'s registers and memory (SCTLR_EL2.I = 1): no fault, PA `{NS, pageOA (leafBase D) va}`,
    Normal inner/outer WB, `vaddress = va`, `t.regs = clrGP u.regs` (so `ProjRegsEq u.regs t.regs`),
    memory unchanged, and the event delta translationStart ++ W ++ translationEnd with
    `TTWReadsOK (walkK s.regs s.mem) va W`. -/
theorem tr_ifE (s : State) (hR : Witness.Regs20 s.regs)
    (hI : _get_SCTLR_EL2_Type_I (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1)
    (va : BitVec 64) (hva : va.toNat < 2^48) (D : BitVec 64) (hWE : WalkFactE s va D)
    (hD : MemM1.WalkFactV.LeafBitsC D) (acc : AccessDescriptor) (hA : AccIF acc) (aligned : Bool)
    (size : Int) (u : State) (hu : u.regs = s.regs) (hum : u.mem = s.mem) :
    ∃ ad t, AArch64_TranslateAddress va acc aligned size u = .ok ad t ∧
      ad.fault.statuscode = .Fault_None ∧
      ad.paddress = { paspace := .PAS_NonSecure, address := MemM1.VA.pageOA (MemM1.LeafFactsG.leafBase D) va } ∧
      ad.memattrs.memtype = .MemType_Normal ∧
      ad.memattrs.inner.attrs = MemAttr_WB ∧ ad.memattrs.outer.attrs = MemAttr_WB ∧
      ad.vaddress = va ∧
      t.regs = MemM1.IF.clrGP u.regs ∧
      (acc.acctype = .AccessType_IFETCH → ArmCert.Premises.TranslationAgreesV1.ProjRegsEq u.regs t.regs) ∧
      (acc.acctype ≠ .AccessType_IFETCH → t.regs = u.regs) ∧
      t.mem = u.mem ∧
      ∃ ti W, t.events = u.events ++ #[Event.translationStart ti] ++ W ++ #[Event.translationEnd ad] ∧
        TTWReadsOK (walkK s.regs s.mem) va W := by
  rcases coreIFRW va hva _ (MemM1.ConsumerV2.leafBase_and D) acc aligned size u _ (by rw [hu]; exact hR) hA
      (walkOKIFRW_regs (walkOKIFRW_of s va D hWE hD acc hA) hu hum) (by rw [hu]; exact hI) with
    ⟨ti, ad, t, W, h, hf, hpa, hmt, hin, hout, hv, hr, hm, he, _, hRW⟩
  refine ⟨ad, t, h, hf, hpa, hmt, hin, hout, hv, hr, fun _ => by rw [hr]; exact MemM1.ConsumerV2.projRegsEq_clrGP _,
    fun e => absurd hA.ifetch e, hm, ti, W, ?_, hRW⟩
  rw [he]; simp only [Array.append_assoc]

/-- **`ConsumerV3.EvIF` for `kmap`** from `WalkFactE` + `LeafBitsC` on every code page, with
    `walk := walkK s.regs s.mem` (TranslateAddress is deterministic, so `tr_ifE`'s result is the
    one `EvIF` quantifies over). -/
theorem evIF_kmap (s : State) (hR : Witness.Regs20 s.regs)
    (hI : _get_SCTLR_EL2_Type_I (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1)
    (P : BitVec 64 → Option MemM1.ConsumerV2.Page)
    (hP : ∀ (va : BitVec 64) (p : MemM1.ConsumerV2.Page), va.toNat < 2^48 → P (va >>> 12) = some p →
      p.code = true → WalkFactE s va p.leaf ∧ MemM1.WalkFactV.LeafBitsC p.leaf) :
    MemM1.ConsumerV3.EvIF (walkK s.regs s.mem) s P := by
  intro u hu hum va p acc aligned size ad t hva hp hc hA h
  rcases hP va p hva hp hc with ⟨hWE, hD⟩
  rcases tr_ifE s hR hI va hva p.leaf hWE hD acc hA aligned size u hu hum with
    ⟨ad', t', h', _, _, _, hin, hout, hv, _, _, _, _, ti, W, he, hRW⟩
  obtain ⟨rfl, rfl⟩ := ok_inj (h.symm.trans h')
  exact ⟨hin, hout, hv, ti, W, he, hRW⟩

#print axioms walkOKIFRW_of
#print axioms tr_ifE
#print axioms evIF_kmap
end MemM1.TrIFE
