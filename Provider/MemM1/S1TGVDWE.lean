import MemM1.S1Callees
import MemM1.VA
import MemM1.S1TGVD
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.S1TGVDWE
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.NoFault MemM1.S1T

open MemM1.S1TGVD (desc_upd7)

/-- The EL2&0 stage-1 data cache is enabled when SCTLR_EL2.C = 1. -/
theorem dcT (s : State) (hC : _get_SCTLR_EL2_Type_C (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1) :
    ∀ t, Frame s t → ∃ u, AArch64_S1DCacheEnabled .Regime_EL20 t = .ok true u ∧ Frame t u := by
  intro t ht
  have hC' : _get_SCTLR_EL2_Type_C (t.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1 := by rw [ht.1]; exact hC
  refine ⟨t, ?_, rfl, rfl, rfl⟩
  unfold AArch64_S1DCacheEnabled
  simp only [Bind.bind, EStateM.bind, readReg, PreSail.readReg_apply, Pure.pure, EStateM.pure]
  rw [show Register.SCTLR_EL2.get t.regs = t.regs.bank_BitVec_64 .SCTLR_EL2 from rfl, hC']
  rfl
#print axioms dcT

/-- `s1t_gvd` with the data cache enabled (SCTLR_EL2.C = 1) and the walk's inner/outer write-back
    attributes, concluding that the stage-1 output descriptor has inner/outer write-back attributes.
    Previously: `MemM1.S1TGV.s1t_gv` with the walked descriptor's bit 7 = 0 (dirty page) in place of
    DBM (bit 51) = 0, so the hardware dirty-state update is the identity whatever its condition.
    Originally: `MemM1.S1TG.s1t_g` at an arbitrary lower-range VA (`va.toNat < 2^48`): S1Translate (EL2&0,
    EL0 NS GPR data access) where the walk parameters and walk outputs are those the actual
    GetS1TTWParams / S1Walk return at `va`; the leaf is a level-3 4K page with 4K-aligned NS
    base `B`, and the output address is `pageOA B va`. Body generated from `MemM1.S1T.s1t`.
    Event-tracking version of `S1TGVDW.s1t_gvdw`: if the walk appends some `W` with `R W`, so
    does S1Translate. Generated from `MemM1.S1TGVDW.s1t_gvdw`. -/
theorem s1t_gvdwe (R : Array Event → Prop) (f : FaultRecord) (va : BitVec 64) (hva : va.toNat < 2^48) (B : BitVec 56)
    (hB : B &&& 0xfff#56 = 0#56)
    (aligned : Bool) (acc : AccessDescriptor) (s : State)
    (oa : FullAddress) (hoa : oa = {paspace := .PAS_NonSecure, address := MemM1.VA.pageOA B va})
    (hf : f.statuscode = .Fault_None)
    (hel : acc.el = 0#2) (hacc : acc.acctype = .AccessType_GPR) (htag : acc.tagaccess = false)
    (hls64 : acc.ls64 = false) (htx : acc.transactional = false)
    (hnf : acc.nonfault = false) (hff : acc.firstfault = false)
    (hPOE : s.regs.FeatureImpl[210] = false) (hGCS : s.regs.FeatureImpl[245] = false)
    (hPAN : s.regs.FeatureImpl[51] = false)
    (hC : _get_SCTLR_EL2_Type_C (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1)
    (hEn : ∀ t, Frame s t → ∃ u,
      AArch64_S1Enabled .Regime_EL20 acc.acctype t = .ok true u ∧ Frame t u)
    (hWP : ∀ t, Frame s t → ∃ wp u,
      AArch64_GetS1TTWParams .Regime_EL20 acc.ss va t = .ok wp u ∧ Frame t u ∧
      wp.d128 = 0#1 ∧ wp.pie = 0#1 ∧ wp.ds = 0#1 ∧ wp.tgx = .TGx_4KB ∧ wp.txsz = 16#6 ∧
      wp.wxn = 0#1 ∧ wp.e0pd = 0#1 ∧
      ∀ (f' : FaultRecord) v, f'.statuscode = .Fault_None → Frame s v → ∃ fw wa w d u',
        AArch64_S1Walk f' wp va .Regime_EL20 acc 64 v = .ok (fw, wa, w, d) u' ∧
        fw.statuscode = .Fault_None ∧ u'.regs = v.regs ∧ u'.mem = v.mem ∧ (∃ W, u'.events = v.events ++ W ∧ R W) ∧
        d.getLsbD 10 = true ∧ d.getLsbD 7 = false ∧
        w.memattrs.memtype = .MemType_Normal ∧
        w.memattrs.inner.attrs = MemAttr_WB ∧ w.memattrs.outer.attrs = MemAttr_WB ∧ w.level = 3 ∧ w.contiguous = 0#1 ∧
        w.baseaddress = {paspace := .PAS_NonSecure, address := B} ∧
        BitVec.setWidth 2 (Sail.BitVec.extractLsb w.permissions.ap 2 1) = 1#2 ∧
        w.permissions.ap_table = 0#2) :
    ∃ fr ipa u, AArch64_S1Translate f .Regime_EL20 va aligned acc s = .ok (fr, ipa) u ∧
      fr.statuscode = .Fault_None ∧ ipa.paddress = oa ∧ ipa.memattrs.memtype = .MemType_Normal ∧
      ipa.memattrs.inner.attrs = MemAttr_WB ∧ ipa.memattrs.outer.attrs = MemAttr_WB ∧
      ipa.fault.statuscode = .Fault_None ∧ u.regs = s.regs ∧ u.mem = s.mem ∧
      ∃ W, u.events = s.events ++ W ∧ R W := by
  have hIF : acc.acctype ≠ .AccessType_IFETCH := by rw [hacc]; intro h; cases h
  have hIFb : (acc.acctype == .AccessType_IFETCH) = false := by
    cases h : acc.acctype <;> first | rfl | exact absurd h hIF
  rcases occ_normal 1608 s with ⟨l1, s1, e1, g1⟩
  rcases accdesc_normal l1 s1 with ⟨da, s2, e2, g2⟩
  rcases occ_normal 1609 s2 with ⟨l3, s3, e3, g3⟩
  rcases S1EntryCalleesExtra.bool_normal l3 s3 with ⟨b4, s4, e4, g4⟩
  rcases occ_normal 1610 s4 with ⟨l5, s5, e5, g5⟩
  rcases S1EntryCalleesExtra.bool_normal l5 s5 with ⟨b6, s6, e6, g6⟩
  rcases occ_normal 1611 s6 with ⟨l7, s7, e7, g7⟩
  rcases tlbline_normal l7 s7 with ⟨tl, s8, e8, g8⟩
  have F8 := frame_trans (frame_trans (frame_trans (frame_trans (frame_trans (frame_trans
    (frame_trans g1 g2) g3) g4) g5) g6) g7) g8
  rcases hEn s8 F8 with ⟨s9, e9, g9⟩
  have F9 := frame_trans F8 g9
  rcases hWP s9 F9 with ⟨wp, s10, e10, g10, hd128, hpie, hdsz, htg, htxsz, hwxn, he0pd, hWalk⟩
  have hE0 : ((acc.el == EL0) && (wp.e0pd == 1#1)) = false := by rw [he0pd]; simp
  have hOOR := MemM1.VA.oorV va hva acc.acctype wp htxsz
  have hMin := S1Callees.minTx wp s hd128 hdsz htg htxsz
  have hMax := S1Callees.maxTx wp s htg htxsz
  have hTxF := S1Callees.txf wp s hd128 hdsz htg htxsz
  have F10 := frame_trans F9 g10
  rcases hMin s10 F10 with ⟨mn, s11, e11, hmn, g11⟩
  have F11 := frame_trans F10 g11
  rcases hMax s11 F11 with ⟨mx, s12, e12, hmx, g12⟩
  have F12 := frame_trans F11 g12
  rcases hTxF s12 F12 with ⟨s13, e13, g13⟩
  have F13 := frame_trans F12 g13
  rcases tme_normal s13 with ⟨tme, s14, e14, g14⟩
  have F14 := frame_trans F13 g14
  rcases sve_normal s14 with ⟨sve, s15, e15, g15⟩
  have F15 := frame_trans F14 g15
  rcases occ_normal 1612 s15 with ⟨l16, s16, e16, g16⟩
  rcases addr l16 s16 with ⟨dipa, s17, e17, g17⟩
  rcases occ_normal 1613 s17 with ⟨l18, s18, e18, g18⟩
  rcases walk_normal l18 s18 with ⟨ws, s19, e19, g19⟩
  rcases occ_normal 1614 s19 with ⟨l20, s20, e20, g20⟩
  rcases bits_normal 128 l20 s20 with ⟨dsc, s21, e21, g21⟩
  rcases occ_normal 1615 s21 with ⟨l22, s22, e22, g22⟩
  rcases bits_normal 128 l22 s22 with ⟨nd, s23, e23, g23⟩
  rcases occ_normal 1616 s23 with ⟨l24, s24, e24, g24⟩
  rcases bits_normal 128 l24 s24 with ⟨md, s25, e25, g25⟩
  have F25 := frame_trans (frame_trans (frame_trans (frame_trans (frame_trans (frame_trans
    (frame_trans (frame_trans (frame_trans (frame_trans F15 g16) g17) g18) g19) g20) g21) g22)
    g23) g24) g25
  have hlt : (decide ((wp.txsz.toNat : Int) < mn)) = false := by simp only [decide_eq_false_iff_not, Int.not_lt]; exact hmn
  have hgt : (decide ((wp.txsz.toNat : Int) > mx)) = false := by simp only [decide_eq_false_iff_not, gt_iff_lt, Int.not_lt]; exact hmx
  have hf0 : ({ { f with secondstage := false } with s2fs1walk := false } : FaultRecord).statuscode
      = .Fault_None := hf
  rcases hWalk _ s25 hf0 F25 with ⟨fw, wa, w, d, s26, e26, hfw, g26r, g26m, ⟨W, g26e, hRW⟩, hAF, hD7, hMT, hin, hout, hl, hc, hb, hap, hapt⟩
  have b26r : s26.regs = s.regs := g26r.trans F25.1
  have b26m : s26.mem = s.mem := g26m.trans F25.2.1
  have b26e : s26.events = s.events ++ W := by rw [g26e, F25.2.2]
  have back : ∀ u, Frame s26 u → u.regs = s.regs ∧ u.mem = s.mem ∧ ∃ W, u.events = s.events ++ W ∧ R W :=
    fun u h => ⟨h.1.trans b26r, h.2.1.trans b26m, W, h.2.2.trans b26e, hRW⟩
  have hDC := dcT s26 (by rw [b26r]; exact hC)
  have hMEC := S1Callees.mec wp (AArch64_GetVARange va) s26
  have hAl := S1Callees.al acc aligned wp.ntlsmd w.memattrs s26 hMT
  have hPerm := S1Callees.perm w wp acc s26 (by rw [b26r]; exact hPOE) (by rw [b26r]; exact hGCS)
    (by rw [b26r]; exact hPAN) hpie hwxn hel hacc htag hap hapt
  have hOA : ∀ t, Frame s26 t → ∃ u, StageOA va wp.d128 wp.tgx w t = .ok oa u ∧ Frame t u := by
    rw [hoa]; exact MemM1.VA.oaV va wp w s26 B hd128 htg hl hc hb hB
  have F26 : Frame s26 s26 := ⟨rfl, rfl, rfl⟩
  rcases hAl s26 F26 with ⟨s27, e27, g27⟩
  have F27 := frame_trans F26 g27
  rcases hPerm fw s27 hfw F27 with ⟨fc, s28, e28, hfc, g28⟩
  have F28 := frame_trans F27 g28
  rcases hOA s28 F28 with ⟨s29, e29, g29⟩
  have F29 := frame_trans F28 g29
  rcases occ_normal 1622 s29 with ⟨l30, s30, e30, g30⟩
  rcases memattrs_normal l30 s30 with ⟨mattr, s31, e31, g31⟩
  have F31 := frame_trans (frame_trans F29 g30) g31
  rcases hDC s31 F31 with ⟨s32, e32, g32⟩
  have F32 := frame_trans F31 g32
  have hfwn : (fw.statuscode != Fault.Fault_None) = false := by rw [hfw]; rfl
  have hfwe : (fw.statuscode == Fault.Fault_None) = true := by rw [hfw]; rfl
  have hfcn : (fc.statuscode != Fault.Fault_None) = false := by rw [hfc]; rfl
  have hfce : (fc.statuscode == Fault.Fault_None) = true := by rw [hfc]; rfl
  have hNN : (MemType.MemType_Normal == MemType.MemType_Normal) = true := rfl
  have hEL : (Regime.Regime_EL20 == Regime.Regime_EL10) = false := rfl
  have hds : AArch64_SettingDirtyStatePermitted fc = pure true := by
    unfold AArch64_SettingDirtyStatePermitted; rw [hfc]; rfl
  have hd128b : (wp.d128 == 1#1) = false := by rw [hd128]; rfl
  have hpieb : (wp.pie == 1#1) = false := by rw [hpie]; rfl
  have haf : AArch64_SettingAccessFlagPermitted fc = pure true := by
    unfold AArch64_SettingAccessFlagPermitted; rw [hfc]; rfl
  have hafd := desc_af dsc d hAF
  have hd7 := desc_upd7 dsc d hD7
  obtain ⟨tlbv, hrd⟩ : ∃ v, (readReg Register.__tlb_enabled : SailM Bool) s28 = EStateM.Result.ok v s28 :=
    ⟨_, rfl⟩
  cases hab : (wp.ha == 1#1)
  all_goals
    unfold AArch64_S1Translate
    simp only [SailME.run, PreSail.PreSailME.run, Bind.bind, Pure.pure, Functor.map, ExceptT.bind,
      ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.lift, ExceptT.run, EStateM.bind, EStateM.map,
      EStateM.pure, liftM, MonadLiftT.monadLift, MonadLift.monadLift,
      e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21,
      e22, e23, e24, e25, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, hlt, hgt, hOOR,
      hE0, htx, hnf, hff, Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, Bool.or_false,
      Bool.false_or]
    rw [show (1048576 : Nat) = 1048575 + 1 from rfl, until_succ]
    simp only [SailME.run, PreSail.PreSailME.run, Bind.bind, Pure.pure, Functor.map, ExceptT.bind,
      ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.lift, ExceptT.run, EStateM.bind, EStateM.map,
      EStateM.pure, liftM, MonadLiftT.monadLift, MonadLift.monadLift,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
      Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, Bool.or_false,
      Bool.false_or, hd128b, hab, haf, hafd, hpieb, hd7, ite_self, e26, hfwn, hIFb, e27, hfwe, e28, hds, bne_self_eq_false, beq_self_eq_true,
      hrd, e29, e30, e31, e32, Bool.true_or, Bool.or_true, bne, hIFb, hMT, beq_self_eq_true, hNN, hfce, hEL, hls64]
    try simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, EStateM.pure]
    rcases create' va oa s32 with ⟨g, s33, hcr, g33⟩
    have F33 := frame_trans F32 g33
    have hcr1 := fun ma => (hcr ma).1
    have hgp := fun ma => (hcr ma).2.1
    have hgm := fun ma => (hcr ma).2.2.1
    have hgf := fun ma => (hcr ma).2.2.2
    rcases hMEC oa.paspace (BitVec.updateSubrange (BitVec.updateSubrange dsc 63 0 d) 127 64 Zeros)
      s33 F33 with ⟨mec, s34, e34, g34⟩
    simp only [Bind.bind, Pure.pure, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, EStateM.bind,
      EStateM.map, EStateM.pure, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, hcr1, hgp,
      e34]
    exact ⟨_, _, _, rfl, hfc, rfl, by simp only [hgm, hMT], by simp only [hgm, hin], by simp only [hgm, hout], by simp only [hgf], back _ (frame_trans F33 g34)⟩

#print axioms s1t_gvdwe
end MemM1.S1TGVDWE
