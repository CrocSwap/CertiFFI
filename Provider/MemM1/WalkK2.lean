import MemM1.M1CoreVDWE2
import MemM1.CoreIFL2
import MemM1.LeafFactsL2
import M1a.Block2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.WalkK2
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality S1OuterSetup ArmCert.Eval.JointSAT ArmCert.Eval.M1a MemM1.Witness
open ArmCert.Eval.M1a.TWP ArmCert.Eval.M1a.WEv ArmCert.Premises.TranslationAgreesV3
open ArmCert.Eval.M1a.B2 (WalkFactE2)
open MemM1.WalkKE (descOf descOf_eq ok_inj)
open MemM1.WitnessVDWE2 (WalkOKVDWR2 coreVDWE2)
open MemM1.CoreIFL2 (WalkOKIFRW2 walkOKIFRW2_regs coreIFRW2)
open MemM1.LeafFactsL2 (blockBase blockBase_aligned)
open MemM1.WitnessIF (AccIF)

/-! Level-2 (2 MB block) leaves: the 3-slot walk PA sequence, the bridges from eval's
`WalkFactE2` to the level-2 event-tracking walk hypotheses, and the per-access AgreesV3 conjuncts.
`TTWReadsOK walk va W` only reads `(walk va).length` and the entries `(walk va).getD i 0`, so a
level-aware `walk` (4 slots for pages, 3 for blocks) is fine. -/

/-- The block walk's PA sequence: root slot (level 0) and the level-1 and level-2 slots. -/
def walkK2 (r : Regs) (mem : S1ResourcePath.Memory) (va : BitVec 64) : List Nat :=
  let s0 := rootSlot r va
  let s1 := S1ResourcePath.nextSlot va 0 (descOf mem s0.address.toNat)
  let s2 := S1ResourcePath.nextSlot va (0 + 1) (descOf mem s1.address.toNat)
  [s0.address.toNat, s1.address.toNat, s2.address.toNat]

theorem readsOK2 (wp : S1TTWParams) (hee : wp.ee = 0#1) (r : Regs) (mem : S1ResourcePath.Memory)
    (va : BitVec 64) (W : Array Event) (h : ReadsAlong wp va mem 3 0 (rootSlot r va) W) :
    TTWReadsOK (walkK2 r mem) va W := by
  have hdec : ∀ x, S2FetchFrame.decoded wp.ee x = x := by
    intro x; unfold S2FetchFrame.decoded; rw [hee]; rfl
  cases h with
  | table desc0 h0 rest0 =>
    cases rest0 with
    | table desc1 h1 rest1 =>
      cases rest1 with
      | leaf h2 =>
        have e0 := descOf_eq _ _ _ desc0
        subst e0
        simp only [hdec] at desc1 h1
        have e1 := descOf_eq _ _ _ desc1
        subst e1
        simp only [hdec] at h2
        refine ⟨rfl, ?_⟩
        intro i hi
        have hi' : i < 3 := by simpa using hi
        rcases i with _ | _ | _ | i
        · exact h0
        · exact h1
        · exact h2
        · omega
      | table _ _ rest2 => cases rest2

theorem blockBase_and (D : BitVec 64) : blockBase D &&& 0x1fffff#56 = 0#56 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x1fffff#56 : BitVec 56).toNat = 2 ^ 21 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, blockBase_aligned]
  rfl

/-- **Bridge (data blocks)**: `WalkFactE2` + data leaf bits ⇒ the level-2 event-tracking walk
    hypothesis with `TTWReadsOK (walkK2 s.regs s.mem) va`. -/
theorem walkOKVDWR2_of (s : State) (va D : BitVec 64) (hWE : WalkFactE2 s va D)
    (hD : MemM1.ConsumerD.LeafBitsD D) (acc : AccessDescriptor) (hA : Acc0 acc) :
    WalkOKVDWR2 acc s va (blockBase D) (TTWReadsOK (walkK2 s.regs s.mem) va) := by
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
    ⟨c, ⟨fw, wa, w, d⟩, x, hcwp, _, _, _, hwalk, ⟨hwr, hwm, hd, hfw, _, cur, m, hcl, hcpas, hcapt, _, _, hlv⟩,
      W, hWev, _, hRA⟩
  subst hcwp
  have hdec : S2FetchFrame.decoded c.wp.ee D = D := by
    unfold S2FetchFrame.decoded; rw [hee]; rfl
  rw [hdec] at hd hlv
  rcases MemM1.LeafFactsL2.leafL2 cur m c.wp D w v.regs hcl hcpas hmair hd128 htg hpie hds haie hcapt
      hD.idx hD.ap hD.cont hlv with ⟨hmt, hin, hout, hap, hapt, hl, hc, hb, _⟩
  have hdD : d = D := hd
  rw [hvm] at hRA
  refine ⟨fw, wa, w, d, x, hwalk, hfw, hwr, hwm, ⟨W, hWev, readsOK2 _ hee s.regs s.mem va W hRA⟩,
    ?_, ?_, hmt, hin, hout, hl, hc, hb, hap, hapt⟩
  · rw [hdD]; exact hD.af
  · rw [hdD]; exact hD.b7

/-- **Bridge (code blocks)**: `WalkFactE2` + code leaf bits ⇒ the level-2 IFETCH walk hypothesis. -/
theorem walkOKIFRW2_of (s : State) (va D : BitVec 64) (hWE : WalkFactE2 s va D)
    (hD : MemM1.WalkFactV.LeafBitsC D) (acc : AccessDescriptor) (hA : AccIF acc) :
    WalkOKIFRW2 acc s va (blockBase D) (TTWReadsOK (walkK2 s.regs s.mem) va) := by
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
    ⟨c, ⟨fw, wa, w, d⟩, x, hcwp, _, _, _, hwalk, ⟨hwr, hwm, hd, hfw, _, cur, m, hcl, hcpas, _, hcuxt, _, hlv⟩,
      W, hWev, _, hRA⟩
  subst hcwp
  have hdec : S2FetchFrame.decoded c.wp.ee D = D := by
    unfold S2FetchFrame.decoded; rw [hee]; rfl
  rw [hdec] at hd hlv
  rcases MemM1.LeafFactsL2.leafL2C_x cur m c.wp D w v.regs hcl hcpas hmair hd128 htg hpie hds haie hcuxt
      hD.idx hD.dbm' hD.cont hD.uxn hD.gp hlv with ⟨hmt, hin, hout, hl, hc, hb, hux, huxt, hgp⟩
  have hdD : d = D := hd
  rw [hvm] at hRA
  refine ⟨fw, wa, w, d, x, hwalk, hfw, hwr, hwm, ⟨W, hWev, readsOK2 _ hee s.regs s.mem va W hRA⟩,
    ?_, ?_, hmt, hin, hout, hl, hc, hb, hux, huxt, hgp⟩
  · rw [hdD]; exact hD.af
  · rw [hdD]; exact hD.dbm

theorem walkOKVDWR2_regs {acc : AccessDescriptor} {s u : State} {va : BitVec 64} {B : BitVec 56}
    {R : Array Event → Prop} (h : WalkOKVDWR2 acc s va B R) (hr : u.regs = s.regs)
    (hm : u.mem = s.mem) : WalkOKVDWR2 acc u va B R := by
  unfold WalkOKVDWR2 at h ⊢
  rw [hr, hm]
  exact h

/-- **AgreesV3 conjuncts for one data access in a 2 MB block.** -/
theorem tr_dataE2 (s : State) (hR : Regs20 s.regs)
    (hC : _get_SCTLR_EL2_Type_C (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1)
    (va : BitVec 64) (hva : va.toNat < 2^48) (D : BitVec 64) (hWE : WalkFactE2 s va D)
    (hD : MemM1.ConsumerD.LeafBitsD D) (acc : AccessDescriptor) (hA : Acc0 acc) (aligned : Bool)
    (size : Int) (u : State) (hu : u.regs = s.regs) (hum : u.mem = s.mem) :
    ∃ ad t, AArch64_TranslateAddress va acc aligned size u = .ok ad t ∧
      ad.fault.statuscode = .Fault_None ∧
      ad.paddress = { paspace := .PAS_NonSecure, address := MemM1.VA2.blockOA (blockBase D) va } ∧
      ad.memattrs.memtype = .MemType_Normal ∧
      ad.memattrs.inner.attrs = MemAttr_WB ∧ ad.memattrs.outer.attrs = MemAttr_WB ∧
      ad.vaddress = va ∧
      (acc.acctype = .AccessType_IFETCH → ArmCert.Premises.TranslationAgreesV1.ProjRegsEq u.regs t.regs) ∧
      (acc.acctype ≠ .AccessType_IFETCH → t.regs = u.regs) ∧
      t.mem = u.mem ∧
      ∃ ti W, t.events = u.events ++ #[Event.translationStart ti] ++ W ++ #[Event.translationEnd ad] ∧
        TTWReadsOK (walkK2 s.regs s.mem) va W := by
  rcases coreVDWE2 _ va hva _ (blockBase_and D) acc aligned size u (by rw [hu]; exact hR) hA
      (walkOKVDWR2_regs (walkOKVDWR2_of s va D hWE hD acc hA) hu hum) (by rw [hu]; exact hC) with
    ⟨ad, t, h, hf, hpa, hmt, hin, hout, hv, hr, hm, ti, W, he, hRW⟩
  refine ⟨ad, t, h, hf, hpa, hmt, hin, hout, hv, fun hk => absurd hk (by rw [hA.gpr]; intro h; cases h),
    fun _ => hr, hm, ti, W, he, hRW⟩

/-- **AgreesV3 conjuncts for one instruction fetch in a 2 MB code block** (SCTLR_EL2.I = 1). -/
theorem tr_ifE2 (s : State) (hR : Regs20 s.regs)
    (hI : _get_SCTLR_EL2_Type_I (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1)
    (va : BitVec 64) (hva : va.toNat < 2^48) (D : BitVec 64) (hWE : WalkFactE2 s va D)
    (hD : MemM1.WalkFactV.LeafBitsC D) (acc : AccessDescriptor) (hA : AccIF acc) (aligned : Bool)
    (size : Int) (u : State) (hu : u.regs = s.regs) (hum : u.mem = s.mem) :
    ∃ ad t, AArch64_TranslateAddress va acc aligned size u = .ok ad t ∧
      ad.fault.statuscode = .Fault_None ∧
      ad.paddress = { paspace := .PAS_NonSecure, address := MemM1.VA2.blockOA (blockBase D) va } ∧
      ad.memattrs.memtype = .MemType_Normal ∧
      ad.memattrs.inner.attrs = MemAttr_WB ∧ ad.memattrs.outer.attrs = MemAttr_WB ∧
      ad.vaddress = va ∧
      (acc.acctype = .AccessType_IFETCH → ArmCert.Premises.TranslationAgreesV1.ProjRegsEq u.regs t.regs) ∧
      (acc.acctype ≠ .AccessType_IFETCH → t.regs = u.regs) ∧
      t.mem = u.mem ∧
      ∃ ti W, t.events = u.events ++ #[Event.translationStart ti] ++ W ++ #[Event.translationEnd ad] ∧
        TTWReadsOK (walkK2 s.regs s.mem) va W := by
  rcases coreIFRW2 va hva _ (blockBase_and D) acc aligned size u _ (by rw [hu]; exact hR) hA
      (walkOKIFRW2_regs (walkOKIFRW2_of s va D hWE hD acc hA) hu hum) (by rw [hu]; exact hI) with
    ⟨ti, ad, t, W, h, hf, hpa, hmt, hin, hout, hv, hr, hm, he, _, hRW⟩
  refine ⟨ad, t, h, hf, hpa, hmt, hin, hout, hv,
    fun _ => by rw [hr]; exact MemM1.ConsumerV2.projRegsEq_clrGP _,
    fun e => absurd hA.ifetch e, hm, ti, W, ?_, hRW⟩
  rw [he]; simp only [Array.append_assoc]

#print axioms readsOK2
#print axioms blockBase_and
#print axioms walkOKVDWR2_of
#print axioms walkOKIFRW2_of
#print axioms tr_dataE2
#print axioms tr_ifE2
end MemM1.WalkK2
