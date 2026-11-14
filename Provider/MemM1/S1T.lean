import MemM1.Full
import GetGuestFields.CalleeNormal
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
namespace MemM1.S1T
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.NoFault

theorem accdesc_normal (l : ChoiceLabel) : Normal (undefined_AccessDescriptor l ()) := by
  intro s
  rw [UndefSummaries.AccessDescriptor_eq]
  delta UndefSummaries.AccessDescriptor_native
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩

theorem tlbline_normal (l : ChoiceLabel) : Normal (undefined_TLBLine l ()) := by
  intro s
  unfold undefined_TLBLine
  rcases S1EntryCalleesExtra.record_normal (l.child 0) s with ⟨r, t, h1, f1⟩
  rcases S1EntryCalleesExtra.bool_normal (l.child 1) t with ⟨b, u, h2, f2⟩
  refine ⟨{ tlbrecord := r, valid_name := b }, u, ?_, frame_trans f1 f2⟩
  simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, h1, h2]

theorem memattrs_normal (l : ChoiceLabel) : Normal (undefined_MemoryAttributes l ()) := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem hints_normal (l : ChoiceLabel) : Normal (undefined_MemAttrHints l ()) := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem cub_normal (u : Unpredictable) : Normal (ConstrainUnpredictableBool u) := by
  intro s
  unfold ConstrainUnpredictableBool
  rcases occ_normal 514 s with ⟨l, t, h1, f1⟩
  rcases S1EntryCalleesExtra.bool_normal l t with ⟨b, u, h2, f2⟩
  exact ⟨b, u, by simp only [Bind.bind, EStateM.bind, h1, h2], frame_trans f1 f2⟩

theorem normalnc (s : State) :
    ∃ m t, NormalNCMemAttr () s = .ok m t ∧ m.memtype = .MemType_Normal ∧ Frame s t := by
  unfold NormalNCMemAttr
  rcases occ_normal 1217 s with ⟨l1, s1, h1, f1⟩
  rcases hints_normal l1 s1 with ⟨nc, s2, h2, f2⟩
  rcases occ_normal 1218 s2 with ⟨l2, s3, h3, f3⟩
  rcases memattrs_normal l2 s3 with ⟨m, s4, h4, f4⟩
  refine ⟨{ m with memtype := .MemType_Normal, outer := { nc with attrs := MemAttr_NC }, inner := { nc with attrs := MemAttr_NC }, shareability := .Shareability_OSH, tags := .MemTag_Untagged, notagaccess := false }, s4, ?_, rfl, frame_trans (frame_trans (frame_trans f1 f2) f3) f4⟩
  simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, h1, h2, h3, h4]

theorem faultrec_normal (l : ChoiceLabel) : Normal (undefined_FaultRecord l ()) := by
  intro s
  rw [UndefSummaries.FaultRecord_eq]
  delta UndefSummaries.FaultRecord_native
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩

theorem nofault0_normal : Normal (NoFault ()) := by
  unfold NoFault __UNKNOWN_AccessDescriptor
  refine bind_normal _ _ (bind_normal _ _ (occ_normal _) fun l => faultrec_normal l) fun f => ?_
  refine bind_normal _ _ (bind_normal _ _ (occ_normal _) fun l => accdesc_normal l) fun a => ?_
  dsimp only
  exact bind_normal _ _ gpc fun g => pure_normal _

theorem nofault0 (s : State) : ∃ f t, NoFault () s = .ok f t ∧ Frame s t := nofault0_normal s

theorem nofault0' (s : State) : ∃ f t, NoFault () s = .ok f t ∧ f.statuscode = .Fault_None ∧ Frame s t := by
  unfold NoFault __UNKNOWN_AccessDescriptor
  rcases occ_normal 884 s with ⟨l1, s1, h1, f1⟩
  rcases faultrec_normal l1 s1 with ⟨fr, s2, h2, f2⟩
  rcases occ_normal 118 s2 with ⟨l2, s3, h3, f3⟩
  rcases accdesc_normal l2 s3 with ⟨a, s4, h4, f4⟩
  rcases gpc s4 with ⟨g, s5, h5, f5⟩
  let nf : FaultRecord := { fr with statuscode := .Fault_None, access := a, secondstage := false, s2fs1walk := false, dirtybit := false, overlay := false, toplevel := false, assuredonly := false, s1tagnotdata := false, tagaccess := false, gpcfs2walk := false, gpcf := g }
  refine ⟨nf, s5, ?_, rfl,
      frame_trans (frame_trans (frame_trans (frame_trans f1 f2) f3) f4) f5⟩
  simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, h1, h2, h3, h4, h5]
  rfl

theorem create (va : BitVec 64) (oa : FullAddress) (ma : MemoryAttributes) (s : State) :
    ∃ a t, CreateAddressDescriptor va oa ma s = .ok a t ∧ a.paddress = oa ∧ a.memattrs = ma ∧
      Frame s t := by
  unfold CreateAddressDescriptor
  rcases occ_normal 1249 s with ⟨l, s1, h1, f1⟩
  rcases addr l s1 with ⟨a, s2, h2, f2⟩
  rcases nofault0 s2 with ⟨nf, s3, h3, f3⟩
  refine ⟨{ { { { { a with paddress := oa } with vaddress := va } with memattrs := ma } with fault := nf } with s1assured := false }, s3, ?_, rfl, rfl, frame_trans (frame_trans f1 f2) f3⟩
  simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, h1, h2, h3]

theorem create' (va : BitVec 64) (oa : FullAddress) (s : State) :
    ∃ (g : MemoryAttributes → AddressDescriptor) (t : State), (∀ ma, CreateAddressDescriptor va oa ma s = .ok (g ma) t ∧
      (g ma).paddress = oa ∧ (g ma).memattrs = ma ∧ (g ma).fault.statuscode = .Fault_None) ∧ Frame s t := by
  unfold CreateAddressDescriptor
  rcases occ_normal 1249 s with ⟨l, s1, h1, f1⟩
  rcases addr l s1 with ⟨a, s2, h2, f2⟩
  rcases nofault0' s2 with ⟨nf, s3, h3, hnf, f3⟩
  refine ⟨fun ma =>
    { { { { { a with paddress := oa } with vaddress := va } with memattrs := ma } with fault := nf } with s1assured := false }, s3, fun ma => ⟨?_, rfl, rfl, hnf⟩, frame_trans (frame_trans f1 f2) f3⟩
  simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, h1, h2, h3]

theorem upd'_getLsbD {w : Nat} (x : BitVec w) (start len : Nat) (y : BitVec len) (i : Nat) (hi : i < w) :
    (Sail.BitVec.updateSubrange' x start len y).getLsbD i =
      if start ≤ i ∧ i < start + len then y.getLsbD (i - start) else x.getLsbD i := by
  simp only [Sail.BitVec.updateSubrange', BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
  by_cases h1 : start ≤ i <;> by_cases h2 : i < start + len
  all_goals simp only [h1, h2, hi, and_self, and_false, false_and, ↓reduceIte, BitVec.getLsbD_eq_getElem]
  all_goals have yge : len ≤ i - start → y.getLsbD (i - start) = false := BitVec.getLsbD_of_ge y _
  all_goals by_cases a : i < start <;> by_cases b : i - start < w <;> by_cases c : i - start < len <;>
    first
      | (simp [a, b, c, yge (by omega)] <;> omega)
      | (simp [a, b, c] <;> omega)

theorem desc_getLsbD (dsc : BitVec 128) (d : BitVec 64) (i : Nat) (hi : i < 128) :
    (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange dsc 63 0 d) 127 64 (Zeros (n := 64))).getLsbD i
      = (decide (i < 64) && d.getLsbD i) := by
  simp only [Sail.BitVec.updateSubrange]
  rw [upd'_getLsbD _ _ _ _ _ hi, upd'_getLsbD _ _ _ _ _ hi]
  have hz : ∀ j, (Zeros (n := 64)).getLsbD j = false := by
    intro j; simp [Zeros, Sail.BitVec.castWidth_eq]
  by_cases h : i < 64
  · simp [h, hz]
  · simp [h, hz]; omega

theorem desc_af (dsc : BitVec 128) (d : BitVec 64) (h : d.getLsbD 10 = true) :
    Sail.BitVec.update (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange dsc 63 0 d) 127 64
      (Zeros (n := 64))) 10 (Bit 1#1) =
    Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange dsc 63 0 d) 127 64 (Zeros (n := 64)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Sail.BitVec.update]
  rw [upd'_getLsbD _ _ _ _ _ hi]
  by_cases h10 : i = 10
  · subst h10
    rw [desc_getLsbD _ _ _ hi, h]
    rfl
  · have : ¬ (10 ≤ i ∧ i < 10 + 1) := by omega
    simp only [this, ↓reduceIte]

theorem desc_dbm (dsc : BitVec 128) (d : BitVec 64) (h : d.getLsbD 51 = false) :
    (BitVec.setWidth 1 (BitVec.join1 [Sail.BitVec.access (Sail.BitVec.updateSubrange
      (Sail.BitVec.updateSubrange dsc 63 0 d) 127 64 (Zeros (n := 64))) 51]) == 1#1) = false := by
  have h51 := desc_getLsbD dsc d 51 (by omega)
  rw [h] at h51
  have : Sail.BitVec.access (Sail.BitVec.updateSubrange
      (Sail.BitVec.updateSubrange dsc 63 0 d) 127 64 (Zeros (n := 64))) 51 = 0#1 := by
    simp only [Sail.BitVec.access]
    rw [getElem!_pos _ 51 (by decide), ← BitVec.getLsbD_eq_getElem, h51]
    rfl
  rw [this]
  rfl

theorem until_succ {m : Type → Type} {α : Type} [Monad m] [MonadLiftT SailM m] (n : Nat)
    (cond : α → m Bool) (init : α) (f : α → m α) :
    sailUntilFuelM (n + 1) cond init f =
      (do let x ← f init; if ← cond x then pure x else sailUntilFuelM n cond x f) := rfl

theorem tme_normal : Normal (HaveTME ()) := by
  rw [GetGuestFeatures.HaveTME.function_eq]; exact GetGuestFields.CalleeNormal.HaveTME
theorem sve_normal : Normal (HaveSVE ()) := by
  rw [GetGuestFeatures.HaveSVE.function_eq]; exact GetGuestFields.CalleeNormal.HaveSVE
theorem mte2_normal : Normal (HaveMTE2Ext ()) := by
  rw [GetGuestFeatures.HaveMTE2Ext.function_eq]; exact GetGuestFields.CalleeNormal.HaveMTE2Ext

/-- M1-b: S1Translate in the EL2&0 regime, for a non-IFETCH, non-LS64 data access, from callee facts. -/
theorem s1t (f : FaultRecord) (va : BitVec 64) (aligned : Bool) (acc : AccessDescriptor) (s : State)
    (wp : S1TTWParams) (wa : AddressDescriptor) (w : TTWState) (d : BitVec 64) (oa : FullAddress)
    (hf : f.statuscode = .Fault_None)
    (hIF : acc.acctype ≠ .AccessType_IFETCH)
    (hls64 : acc.ls64 = false)
    (htx : acc.transactional = false)
    (hnf : acc.nonfault = false)
    (hff : acc.firstfault = false)
    (hd128 : wp.d128 = 0#1)
    (hpie : wp.pie = 0#1)
    (hAF : d.getLsbD 10 = true)
    (hDBM : d.getLsbD 51 = false)
    (hE0 : ((acc.el == EL0) && (wp.e0pd == 1#1)) = false)
    (hOOR : AArch64_VAIsOutOfRange va acc.acctype .Regime_EL20 wp = false)
    (hMT : w.memattrs.memtype = .MemType_Normal)
    (hEn : ∀ t, Frame s t → ∃ u,
      AArch64_S1Enabled .Regime_EL20 acc.acctype t = .ok true u ∧ Frame t u)
    (hWP : ∀ t, Frame s t → ∃ u,
      AArch64_GetS1TTWParams .Regime_EL20 acc.ss va t = .ok wp u ∧ Frame t u)
    (hMin : ∀ t, Frame s t → ∃ m u,
      AArch64_S1MinTxSZ .Regime_EL20 wp.d128 wp.ds wp.tgx t = .ok m u ∧
        m ≤ (wp.txsz.toNat : Int) ∧ Frame t u)
    (hMax : ∀ t, Frame s t → ∃ m u,
      AArch64_MaxTxSZ wp.tgx t = .ok m u ∧ (wp.txsz.toNat : Int) ≤ m ∧ Frame t u)
    (hTxF : ∀ t, Frame s t → ∃ u,
      AArch64_S1TxSZFaults .Regime_EL20 wp t = .ok false u ∧ Frame t u)
    (hWalk : ∀ (f' : FaultRecord) t, f'.statuscode = .Fault_None → Frame s t → ∃ fw u,
      AArch64_S1Walk f' wp va .Regime_EL20 acc 64 t = .ok (fw, wa, w, d) u ∧
        fw.statuscode = .Fault_None ∧ Frame t u)
    (hAl : ∀ t, Frame s t → ∃ u,
      AArch64_S1HasAlignmentFault acc aligned wp.ntlsmd w.memattrs t = .ok false u ∧ Frame t u)
    (hPerm : ∀ (f' : FaultRecord) t, f'.statuscode = .Fault_None → Frame s t → ∃ fc u,
      AArch64_S1CheckPermissions f' .Regime_EL20 w wp acc t = .ok fc u ∧
        fc.statuscode = .Fault_None ∧ Frame t u)
    (hOA : ∀ t, Frame s t → ∃ u, StageOA va wp.d128 wp.tgx w t = .ok oa u ∧ Frame t u)
    (hDC : ∀ t, Frame s t → ∃ b u, AArch64_S1DCacheEnabled .Regime_EL20 t = .ok b u ∧ Frame t u)
    (hMEC : ∀ (pas : PASpace) (desc : BitVec 128) t, Frame s t → ∃ m u,
      AArch64_S1OutputMECID wp .Regime_EL20 (AArch64_GetVARange va) pas desc t = .ok m u ∧
        Frame t u) :
    ∃ fr ipa u, AArch64_S1Translate f .Regime_EL20 va aligned acc s = .ok (fr, ipa) u ∧
      fr.statuscode = .Fault_None ∧ ipa.paddress = oa ∧ ipa.memattrs.memtype = .MemType_Normal ∧
      ipa.fault.statuscode = .Fault_None ∧ Frame s u := by
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
  rcases hWP s9 F9 with ⟨s10, e10, g10⟩
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
  rcases hWalk _ s25 hf0 F25 with ⟨fw, s26, e26, hfw, g26⟩
  have F26 := frame_trans F25 g26
  rcases hAl s26 F26 with ⟨s27, e27, g27⟩
  have F27 := frame_trans F26 g27
  rcases hPerm fw s27 hfw F27 with ⟨fc, s28, e28, hfc, g28⟩
  have F28 := frame_trans F27 g28
  rcases hOA s28 F28 with ⟨s29, e29, g29⟩
  have F29 := frame_trans F28 g29
  rcases occ_normal 1622 s29 with ⟨l30, s30, e30, g30⟩
  rcases memattrs_normal l30 s30 with ⟨mattr, s31, e31, g31⟩
  have F31 := frame_trans (frame_trans F29 g30) g31
  rcases hDC s31 F31 with ⟨dc, s32, e32, g32⟩
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
  have hdbm := desc_dbm dsc d hDBM
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
      Bool.false_or, hd128b, hab, haf, hafd, hpieb, hdbm, ite_self, e26, hfwn, hIFb, e27, hfwe, e28, hds, bne_self_eq_false, beq_self_eq_true,
      hrd, e29, e30, e31, e32, Bool.true_or, Bool.or_true, bne, hIFb, hMT, beq_self_eq_true, hNN, hfce, hEL, hls64]
    cases dc
    · simp only [Bool.not_false, ↓reduceIte, EStateM.pure]
      rcases normalnc s32 with ⟨nc, s33, e33, hncm, g33⟩
      have F33 := frame_trans F32 g33
      rcases mte2_normal s33 with ⟨m2, s34, e34, g34⟩
      have F34 := frame_trans F33 g34
      cases hc : (m2 && w.memattrs.tags == MemTagType.MemTag_AllocationTagged)
      · rcases create' va oa s34 with ⟨g, s35, hcr, g35⟩
        have F35 := frame_trans F34 g35
        have hcr1 := fun ma => (hcr ma).1
        have hgp := fun ma => (hcr ma).2.1
        have hgm := fun ma => (hcr ma).2.2.1
        have hgf := fun ma => (hcr ma).2.2.2
        rcases hMEC oa.paspace (BitVec.updateSubrange (BitVec.updateSubrange dsc 63 0 d) 127 64 Zeros)
          s35 F35 with ⟨mec, s36, e36, g36⟩
        simp only [Bind.bind, Pure.pure, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, EStateM.bind,
          EStateM.map, EStateM.pure, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, e33, e34,
          hc, hcr1, hgp, e36]
        exact ⟨_, _, _, rfl, hfc, rfl, by simp only [hgm, hncm], by simp only [hgf], frame_trans F35 g36⟩
      · rcases cub_normal .Unpredictable_S1CTAGGED s34 with ⟨cb, s35, e35, g35⟩
        have F35 := frame_trans F34 g35
        rcases create' va oa s35 with ⟨g, s36, hcr, g36⟩
        have F36 := frame_trans F35 g36
        have hcr1 := fun ma => (hcr ma).1
        have hgp := fun ma => (hcr ma).2.1
        have hgm := fun ma => (hcr ma).2.2.1
        have hgf := fun ma => (hcr ma).2.2.2
        rcases hMEC oa.paspace (BitVec.updateSubrange (BitVec.updateSubrange dsc 63 0 d) 127 64 Zeros)
          s36 F36 with ⟨mec, s37, e37, g37⟩
        cases cb <;>
        simp only [Bind.bind, Pure.pure, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, EStateM.bind,
          EStateM.map, EStateM.pure, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, e33, e34,
          hc, e35, hcr1, hgp, e37] <;>
        exact ⟨_, _, _, rfl, hfc, rfl, by simp only [hgm, hncm], by simp only [hgf], frame_trans F36 g37⟩
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, EStateM.pure]
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
      exact ⟨_, _, _, rfl, hfc, rfl, by simp only [hgm, hMT], by simp only [hgf], frame_trans F33 g34⟩

#print axioms s1t

end MemM1.S1T
