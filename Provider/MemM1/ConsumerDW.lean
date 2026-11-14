import MemM1.ConsumerD
import MemM1.M1CoreVDW
import MemM1.LeafFactsGW
import MemM1.MemReadD2
import MemM1.MemWriteD7
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
namespace MemM1.ConsumerDW
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality S1OuterSetup ArmCert.Eval.JointSAT ArmCert.Eval.M1a MemM1.Witness MemM1.WalkFactV
open ArmCert.Premises.TranslationAgreesV1 ArmBridge.BoundaryV2 MemM1.ConsumerV2 MemM1.ConsumerD
open MemM1.WitnessVDW (WalkOKVDW coreVDW)
open MemM1.MemReadD2 (E17S)
open MemM1.MemWriteD7 (StrongTA)

/-! The strong translation premise (`MemReadD2.E17S`, `MemWriteD7.StrongTA`) for the page-keyed
consumer map `kmap`, for DATA pages. On top of `ConsumerD.agreesKD` it needs SCTLR_EL2.C = 1 (data
cache enabled; otherwise S1Translate returns Normal non-cacheable attributes) and gives
`vaddress = va` and inner/outer write-back attributes (leaf AttrIndx 0/1, MAIR byte 0xff).

E17S quantifies over every permitted access with `t.regs = u.regs`. On a code page `kmap`
permits instruction fetches, and an IFETCH TranslateAddress changes registers (`IF.clrGP`), so
E17S cannot hold for a map with code pages. `e17s_kmap` therefore assumes every page is a data
page; `e17s_dataOnly` applies it to the data part of any page table, and `strongTA_kmap` gives the
write-side premise for a data page of any page table (code pages allowed). -/

/-- `ConsumerD.walkOKVD_of` with the walk state's inner/outer write-back attributes. -/
theorem walkOKVDW_of (s : State) (va D : BitVec 64) (hW : WalkFact s va D) (hD : LeafBitsD D)
    (acc : AccessDescriptor) (hA : Acc0 acc) :
    WalkOKVDW acc s va (MemM1.LeafFactsG.leafBase D) := by
  intro t htr htm
  let f0 : FaultRecord := { (default : FaultRecord) with statuscode := .Fault_None }
  rcases hW t htr htm f0 acc rfl hA.ss with ⟨wp, u, hg, hfr, hF, hAct, _⟩
  rcases hF with ⟨hee, hwxn, _, _, hpie, _, he0pd, _⟩
  rcases hAct with ⟨htg, hd128, haie, hds, hmair, htx, _⟩
  refine ⟨wp, u, hg, hfr, hd128, hpie, hds, htg, htx, hwxn, he0pd, ?_⟩
  intro f' v hf' hvr hvm
  rcases hW t htr htm f' acc hf' hA.ss with ⟨wp', u', hg', _, _, _, Hv⟩
  obtain rfl : wp' = wp := (ok_inj (hg'.symm.trans hg)).1
  rcases Hv v (hvr.trans htr.symm) (hvm.trans htm.symm) with
    ⟨c, ⟨fw, wa, w, d⟩, x, hcwp, _, _, _, hwalk, hwr, hwm, hd, hfw, _, cur, m, hcl, hcpas, hcapt, _, _, hlv⟩
  subst hcwp
  have hdec : S2FetchFrame.decoded c.wp.ee D = D := by
    unfold S2FetchFrame.decoded; rw [hee]; rfl
  rw [hdec] at hd hlv
  rcases MemM1.LeafFactsGW.leafGW cur m c.wp D w v.regs hcl hcpas hmair hd128 htg hpie hds haie hcapt
      hD.idx hD.ap hD.cont hlv with ⟨hmt, hin, hout, hap, hapt, hl, hc, hb, _⟩
  have hdD : d = D := hd
  refine ⟨fw, wa, w, d, x, hwalk, hfw, hwr, hwm, ?_, ?_, hmt, hin, hout, hl, hc, hb, hap, hapt⟩
  · rw [hdD]; exact hD.af
  · rw [hdD]; exact hD.b7

theorem walkOKVDW_regs {acc : AccessDescriptor} {s u : State} {va : BitVec 64} {B : BitVec 56}
    (h : WalkOKVDW acc s va B) (hr : u.regs = s.regs) (hm : u.mem = s.mem) :
    WalkOKVDW acc u va B := by
  unfold WalkOKVDW at h ⊢
  rw [hr, hm]
  exact h

/-- The data-page TranslateAddress facts E17S / StrongTA need, on any state with `s`'s registers
    and memory. -/
theorem tr_data (s : State) (hR : Regs20 s.regs)
    (hC : _get_SCTLR_EL2_Type_C (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1)
    (va : BitVec 64) (hva : va.toNat < 2^48) (D : BitVec 64) (hW : WalkFact s va D)
    (hD : LeafBitsD D) (acc : AccessDescriptor) (hA : Acc0 acc) (aligned : Bool) (size : Int)
    (u : State) (hu : u.regs = s.regs) (hum : u.mem = s.mem) :
    ∃ ad t, AArch64_TranslateAddress va acc aligned size u = .ok ad t ∧
      ad.fault.statuscode = .Fault_None ∧
      ad.paddress = FullAddress.mk .PAS_NonSecure (MemM1.VA.pageOA (MemM1.LeafFactsG.leafBase D) va) ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ ad.vaddress = va ∧
      t.regs = u.regs ∧ t.mem = u.mem :=
  coreVDW va hva _ (leafBase_and D) acc aligned size u (by rw [hu]; exact hR) hA
    (walkOKVDW_regs (walkOKVDW_of s va D hW hD acc hA) hu hum) (by rw [hu]; exact hC)

/-- **E17S for `kmap`** when every page is a data page. -/
theorem e17s_kmap (s : State) (hR : Regs20 s.regs)
    (hC : _get_SCTLR_EL2_Type_C (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1)
    (P : BitVec 64 → Option Page)
    (hP : ∀ (va : BitVec 64) (p : Page), va.toNat < 2^48 → P (va >>> 12) = some p →
      WalkFact s va p.leaf ∧ (if p.code then LeafBitsC p.leaf else LeafBitsD p.leaf))
    (hdata : ∀ n p, P n = some p → p.code = false) :
    E17S (kmap P) s := by
  refine ⟨fun u hu hum va acc aligned size ⟨hva, _, _, p, hp, hacc⟩ => ?_⟩
  rcases hP va p hva hp with ⟨hW, hD⟩
  have hc := hdata _ p hp
  simp only [hc, Bool.false_eq_true, ↓reduceIte] at hacc hD
  rw [pa_eq P va p hp]
  exact tr_data s hR hC va hva p.leaf hW hD acc hacc aligned size u hu hum

/-- The data part of a page table. -/
def dataOnly (P : BitVec 64 → Option Page) (n : BitVec 64) : Option Page :=
  match P n with
  | some p => if p.code then none else some p
  | none => none

theorem dataOnly_some (P : BitVec 64 → Option Page) (n : BitVec 64) (p : Page)
    (h : dataOnly P n = some p) : P n = some p ∧ p.code = false := by
  unfold dataOnly at h
  split at h
  · rename_i q hq
    cases hqc : q.code
    · rw [hqc] at h
      simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h; exact ⟨hq, hqc⟩
    · rw [hqc] at h; simp at h
  · cases h

/-- **E17S for the data pages of any page table** (hypotheses exactly as `ConsumerD.agreesKD`). -/
theorem e17s_dataOnly (s : State) (hR : Regs20 s.regs)
    (hC : _get_SCTLR_EL2_Type_C (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1)
    (P : BitVec 64 → Option Page)
    (hP : ∀ (va : BitVec 64) (p : Page), va.toNat < 2^48 → P (va >>> 12) = some p →
      WalkFact s va p.leaf ∧ (if p.code then LeafBitsC p.leaf else LeafBitsD p.leaf)) :
    E17S (kmap (dataOnly P)) s :=
  e17s_kmap s hR hC (dataOnly P)
    (fun va p hva h => hP va p hva (dataOnly_some P _ p h).1)
    (fun n p h => (dataOnly_some P n p h).2)

/-- E17S gives the write side's StrongTA for every permitted access. -/
theorem E17S.toStrongTA {m : ConsumerMap} {s : State} (h : E17S m s) (a : BitVec 64)
    (acc : AccessDescriptor) (n : Nat) (hp : m.permitted a acc true (n : Int)) :
    StrongTA a acc n (m.pa a) s := by
  intro u hu hum
  rcases h.tr u hu hum a acc true _ hp with ⟨ad, t, ht, hf, hpa, hmt, _, _, hv, hr, hm⟩
  exact ⟨ad, t, ht, hf, hpa, hmt, hv, hr, hm⟩

/-- **StrongTA for a data page of `kmap P`** (code pages allowed elsewhere in `P`). -/
theorem strongTA_kmap (s : State) (hR : Regs20 s.regs)
    (hC : _get_SCTLR_EL2_Type_C (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1)
    (P : BitVec 64 → Option Page)
    (hP : ∀ (va : BitVec 64) (p : Page), va.toNat < 2^48 → P (va >>> 12) = some p →
      WalkFact s va p.leaf ∧ (if p.code then LeafBitsC p.leaf else LeafBitsD p.leaf))
    (a : BitVec 64) (acc : AccessDescriptor) (n : Nat) (p : Page)
    (ha : a.toNat < 2^48) (hpa : P (a >>> 12) = some p) (hcode : p.code = false)
    (hA : Acc0 acc) :
    StrongTA a acc n ((kmap P).pa a) s := by
  intro u hu hum
  rcases hP a p ha hpa with ⟨hW, hD⟩
  simp only [hcode, Bool.false_eq_true, ↓reduceIte] at hD
  rw [pa_eq P a p hpa]
  rcases tr_data s hR hC a ha p.leaf hW hD acc hA true _ u hu hum with
    ⟨ad, t, ht, hf, hpa', hmt, _, _, hv, hr, hm⟩
  exact ⟨ad, t, ht, hf, hpa', hmt, hv, hr, hm⟩

#print axioms walkOKVDW_of
#print axioms tr_data
#print axioms e17s_kmap
#print axioms e17s_dataOnly
#print axioms E17S.toStrongTA
#print axioms strongTA_kmap
end MemM1.ConsumerDW
