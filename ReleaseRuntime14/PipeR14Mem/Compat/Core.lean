-- C1 compatibility: actual anchors + legacy-VA padding fallback; no padding/padding injectivity premise.
import PipeR14Mem.Static
import ArmCertValue.PhysicalMemory
import TranslateSpan.Regions
open Sail ArmFull ArmCertWalk ArmCert.Translate.Model ArmCertValue
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace PipeR14.Compat

def DataPA (mapping : BitVec 64 → Option Nat) (p : R14E17.Pins) (sites : List (R14Plan.Base × Nat)) (a : Nat) : Prop :=
  ∃ s ∈ sites, ∃ pa, mapping (R14E17.dataVA p s.1) = some pa ∧ pa ≤ a ∧ a < pa+s.2

def hybridView (p : R14E17.Pins) (anchors : List TranslateSpan.Site)
    (mapping : BitVec 64 → Option Nat) (r : Region) (j : Nat) : Option Nat :=
  match TranslateSpan.selected anchors (r,j) with
  | none => mapping (PipeR14.regionVA p r j)
  | some s => (mapping s.start).map (· + (j - s.first))

theorem gap_identity (p : R14E17.Pins) (anchors : List TranslateSpan.Site)
    (mapping : BitVec 64 → Option Nat) (r : Region) (j : Nat)
    (gap : TranslateSpan.selected anchors (r,j) = none) :
    hybridView p anchors mapping r j = mapping (PipeR14.regionVA p r j) := by
  simp only [hybridView,gap]

theorem covered_identity (p : R14E17.Pins) (anchors : List TranslateSpan.Site)
    (mapping : BitVec 64 → Option Nat) (r : Region) (j : Nat) (s : TranslateSpan.Site)
    (covered : TranslateSpan.selected anchors (r,j) = some s) :
    hybridView p anchors mapping r j = TranslateSpan.siteView anchors mapping r j := by
  simp only [hybridView,TranslateSpan.siteView,covered,Option.bind_some]

structure AnchorSources (p : R14E17.Pins) (sites : List (R14Plan.Base × Nat))
    (regions : List Region) (anchors : List TranslateSpan.Site) : Prop where
  actual : ∀ s ∈ anchors, ∃ a ∈ sites,
    s.start = R14E17.dataVA p a.1 ∧ s.size = a.2 ∧
    (s.size = 1 ∨ s.size = 4 ∨ s.size = 8 ∨ s.size = 16) ∧
    s.region ∈ regions ∧ s.first + s.size ≤ 8 * s.region.words ∧
    (∀ t, t < s.size → PipeR14.regionVA p s.region (s.first + t) = s.start + BitVec.ofNat 64 t)

theorem covered_of_layout {p : R14E17.Pins} {sites : List (R14Plan.Base × Nat)}
    {regions : List Region} {anchors : List TranslateSpan.Site}
    (src : AnchorSources p sites regions anchors)
    (distinct : ∀ r ∈ regions, ∀ r' ∈ regions, ∀ j j', j < 8*r.words → j' < 8*r'.words →
      PipeR14.regionVA p r j = PipeR14.regionVA p r' j' → r=r' ∧ j=j')
    (s : TranslateSpan.Site) (hs : s ∈ anchors) (r : Region) (hr : r ∈ regions) (j0 n : Nat)
    (hn : n ≤ s.size) (pos : 0 < n) (hw : j0+n ≤ 8*r.words)
    (layout : ∀ t, t < n → PipeR14.regionVA p r (j0+t) = s.start + BitVec.ofNat 64 t) :
    ∀ t, t < n → (TranslateSpan.selected anchors (r,j0+t)).isSome = true := by
  obtain ⟨a,ha,_,_,_,hsr,hsw,sl⟩ := src.actual s hs
  have l0 := layout 0 pos
  have s0 := sl 0 (by omega)
  simp only [Nat.add_zero,BitVec.add_zero] at l0 s0
  obtain ⟨rfl,rfl⟩ := distinct r hr s.region hsr j0 s.first (by omega) (by omega) (l0.trans s0.symm)
  intro t ht
  obtain ⟨q,hq⟩ := TranslateSpan.selected_exists (sites:=anchors) (a:=(s.region,s.first+t))
    ⟨s,hs,by simp only [TranslateSpan.covers,decide_eq_true_eq];exact ⟨True.intro,by omega,by omega⟩⟩
  simp only [hq,Option.isSome_some]

theorem hybrid_eq_legacy {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins}
    {footprint : Nat → Prop} {sites : List (R14Plan.Base × Nat)} {regions : List Region}
    {anchors : List TranslateSpan.Site} {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint sites regions sc base)
    (src : AnchorSources p sites regions anchors) (r : Region) (j : Nat) :
    hybridView p anchors mapping r j = mapping (PipeR14.regionVA p r j) := by
  cases sel : TranslateSpan.selected anchors (r,j) with
  | none => exact gap_identity p anchors mapping r j sel
  | some s =>
    obtain ⟨hs,he,lo,hi⟩ := TranslateSpan.selected_mem sel
    change s.region = r at he
    obtain ⟨a,ha,start,size,_,_,_,layout⟩ := src.actual s hs
    obtain ⟨pa,mp,_,_,_,contig⟩ := ds.site a ha
    have ht : j - s.first < s.size := by omega
    have va : PipeR14.regionVA p r j = s.start + BitVec.ofNat 64 (j - s.first) := by
      have e : s.first + (j - s.first) = j := by omega
      simpa only [he,e] using layout _ ht
    have ma : mapping s.start = some pa.toNat := by rw [start];exact mp
    have mc : mapping (s.start + BitVec.ofNat 64 (j - s.first)) = some (pa.toNat + (j - s.first)) := by
      rw [start];exact contig _ (by rw [←size];exact ht)
    simp only [hybridView,sel,ma,Option.map_some,va,mc]

theorem legacy_nonalias {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins}
    {footprint : Nat → Prop} {sites : List (R14Plan.Base × Nat)} {regions : List Region}
    {anchors : List TranslateSpan.Site} {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint sites regions sc base)
    (src : AnchorSources p sites regions anchors) : TranslateSpan.SpanNonalias anchors mapping := by
  intro s hs t ht i j hi hj pa pb ma mb same
  obtain ⟨a,ha,ast,asz,asu,ar,ab,al⟩ := src.actual s hs
  obtain ⟨b,hb,bst,bsz,bsu,br,bb,bl⟩ := src.actual t ht
  obtain ⟨qa,mqa,_,_,aa,ca⟩ := ds.site a ha
  obtain ⟨qb,mqb,_,_,ba,cb⟩ := ds.site b hb
  have ea : qa.toNat = pa := Option.some.inj (mqa.symm.trans (by rw [←ast];exact ma))
  have eb : qb.toNat = pb := Option.some.inj (mqb.symm.trans (by rw [←bst];exact mb))
  have mia : mapping (PipeR14.regionVA p s.region (s.first + i)) = some (pa + i) := by
    rw [al i hi,ast];simpa only [ea] using ca i (by rw [←asz];exact hi)
  have mib : mapping (R14E17.dataVA p b.1 + BitVec.ofNat 64 j) = some (pa + i) := by
    rw [same];simpa only [eb] using cb j (by rw [←bsz];exact hj)
  have eq := ds.inj s.region ar (s.first + i) (by omega) b hb j (by rw [←bsz];exact hj) (pa + i) mia mib
  have eq' : s.start + BitVec.ofNat 64 i = t.start + BitVec.ofNat 64 j := by
    rw [←al i hi,bst];exact eq
  have ag := TranslateSpan.aligned_span s.start s.size asu (by rw [ast,asz];exact aa) i hi
  have bg := TranslateSpan.aligned_span t.start t.size bsu (by rw [bst,bsz];exact ba) j hj
  exact ag.1.symm.trans ((congrArg BitVec.toNat eq').trans bg.1)

/-- Every actual-span write misses all other tracked bytes, including the padding fallback. -/
theorem legacy_store_miss {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins}
    {footprint : Nat → Prop} {sites : List (R14Plan.Base × Nat)} {regions : List Region}
    {anchors : List TranslateSpan.Site} {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint sites regions sc base)
    (src : AnchorSources p sites regions anchors) (s : TranslateSpan.Site) (hs : s ∈ anchors)
    (pa : Nat) (mp : mapping s.start = some pa) :
    ∀ r ∈ regions, ∀ j, j < 8 * r.words → ¬ (r = s.region ∧ s.first ≤ j ∧ j < s.first + s.size) →
      ∀ q, hybridView p anchors mapping r j = some q → ¬ (pa ≤ q ∧ q < pa + s.size) := by
  obtain ⟨a,ha,start,size,_,hr,hw,layout⟩ := src.actual s hs
  obtain ⟨qa,mqa,_,_,_,ca⟩ := ds.site a ha
  have ea : qa.toNat = pa := Option.some.inj (mqa.symm.trans (by rw [←start];exact mp))
  have lin : ∀ t, t < a.2 → mapping (R14E17.dataVA p a.1 + BitVec.ofNat 64 t) = some (pa+t) := by
    intro t ht;simpa only [ea] using ca t ht
  intro r hr' j hj nf q hq
  rw [hybrid_eq_legacy ds src] at hq
  exact PipeR14.miss_of ds ha hr (n:=s.size) (by rw [size]; omega) hw lin
    (fun t ht => by rw [←start];exact (layout t ht).symm) r hr' j hj nf q hq

theorem legacy_miss_all {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins}
    {footprint : Nat → Prop} {sites : List (R14Plan.Base × Nat)} {regions : List Region}
    {anchors : List TranslateSpan.Site} {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint sites regions sc base)
    (src : AnchorSources p sites regions anchors)
    (s : R14Plan.Base × Nat) (hs : s ∈ sites) (r : Region) (hr : r ∈ regions) (j0 n : Nat)
    (hn : n ≤ s.2) (hw : j0+n ≤ 8*r.words)
    (layout : ∀ t, t < n → PipeR14.regionVA p r (j0+t) = R14E17.dataVA p s.1 + BitVec.ofNat 64 t)
    (pa : Nat) (mp : mapping (R14E17.dataVA p s.1) = some pa) :
    ∀ r' ∈ regions, ∀ j, j < 8*r'.words → ¬ (r'=r ∧ j0 ≤ j ∧ j < j0+n) →
    ∀ q, hybridView p anchors mapping r' j = some q → ¬ (pa ≤ q ∧ q < pa+n) := by
  obtain ⟨qa,mqa,_,_,_,ca⟩ := ds.site s hs
  have ea : qa.toNat = pa := Option.some.inj (mqa.symm.trans mp)
  intro r' hr' j hj nf q mq
  rw [hybrid_eq_legacy ds src] at mq
  exact PipeR14.miss_of ds hs hr hn hw (fun t ht => by simpa only [ea] using ca t ht)
    (fun t ht => (layout t ht).symm) r' hr' j hj nf q mq

/-- Hybrid-view deployment statics: no interior-VA contiguity field and no padding/padding injectivity. -/
structure DataStartsR14 (mapping : BitVec 64 → Option Nat) (p : R14E17.Pins)
    (footprint : Nat → Prop) (sites : List (R14Plan.Base × Nat)) (regions : List Region)
    (anchors : List TranslateSpan.Site) (sc : Nat → Prop) (base : BitVec 64) : Prop where
  site : ∀ s ∈ sites, ∃ pa : BitVec 56, mapping (R14E17.dataVA p s.1) = some pa.toNat ∧
    MemM1.MemReadIF.NotMMIO pa ∧ (∀ t, t < s.2 → ¬ footprint (pa.toNat+t)) ∧
    (R14E17.dataVA p s.1).toNat % s.2 = 0
  sp16 : p.regs 31 % 16 = 0
  code : ImageTableSeparated sc base mapping (DataPA mapping p sites)
  distinct : ∀ r ∈ regions, ∀ r' ∈ regions, ∀ j j', j < 8*r.words → j' < 8*r'.words →
    PipeR14.regionVA p r j = PipeR14.regionVA p r' j' → r = r' ∧ j = j'
  nonalias : TranslateSpan.SpanNonalias anchors mapping
  storeMiss : ∀ s ∈ anchors, ∀ pa, mapping s.start = some pa →
    ∀ r ∈ regions, ∀ j, j < 8*r.words → ¬ (r = s.region ∧ s.first ≤ j ∧ j < s.first+s.size) →
    ∀ q, hybridView p anchors mapping r j = some q → ¬ (pa ≤ q ∧ q < pa+s.size)
  missAll : ∀ s ∈ sites, ∀ r ∈ regions, ∀ j0 n, n ≤ s.2 → j0+n ≤ 8*r.words →
    (∀ t, t < n → PipeR14.regionVA p r (j0+t) = R14E17.dataVA p s.1 + BitVec.ofNat 64 t) →
    ∀ pa, mapping (R14E17.dataVA p s.1) = some pa →
    ∀ r' ∈ regions, ∀ j, j < 8*r'.words → ¬ (r'=r ∧ j0 ≤ j ∧ j < j0+n) →
    ∀ q, hybridView p anchors mapping r' j = some q → ¬ (pa ≤ q ∧ q < pa+n)
  paddingOutsideActualWrites : ∀ s ∈ anchors, ∀ pa, mapping s.start = some pa →
    ∀ r ∈ regions, ∀ j, j < 8*r.words → TranslateSpan.selected anchors (r,j) = none →
    ∀ q, mapping (PipeR14.regionVA p r j) = some q → ¬ (pa ≤ q ∧ q < pa+s.size)

theorem starts_of_legacy {mapping : BitVec 64 → Option Nat} {p : R14E17.Pins}
    {footprint : Nat → Prop} {sites : List (R14Plan.Base × Nat)} {regions : List Region}
    {anchors : List TranslateSpan.Site} {sc : Nat → Prop} {base : BitVec 64}
    (ds : PipeR14.DataStaticR14 mapping p footprint sites regions sc base)
    (src : AnchorSources p sites regions anchors) : DataStartsR14 mapping p footprint sites regions anchors sc base := by
  refine ⟨?_,ds.sp16,?_,ds.distinct,legacy_nonalias ds src,legacy_store_miss ds src,legacy_miss_all ds src,?_⟩
  · intro s hs
    obtain ⟨pa,mp,mmio,out,align,_⟩ := ds.site s hs
    exact ⟨pa,mp,mmio,out,align⟩
  · intro o pa inside mapped ⟨s,hs,q,mp,lo,hi⟩
    obtain ⟨qa,mqa,_,_,_,ca⟩ := ds.site s hs
    have eq : qa.toNat = q := Option.some.inj (mqa.symm.trans mp)
    apply ds.code o pa inside mapped
    refine ⟨s,hs,pa-q,by omega,?_⟩
    have h := ca (pa-q) (by omega)
    simpa only [eq,show q + (pa-q) = pa by omega] using h
  · intro s hs pa mp r hr j hj gap q mq
    apply legacy_store_miss ds src s hs pa mp r hr j hj ?_ q
      (by rw [gap_identity p anchors mapping r j gap];exact mq)
    intro ⟨eq,lo,hi⟩
    have no := List.find?_eq_none.1 gap s hs
    apply no
    simp only [TranslateSpan.covers,decide_eq_true_eq]
    exact ⟨eq.symm,lo,hi⟩

#print axioms hybrid_eq_legacy
#print axioms legacy_nonalias
#print axioms legacy_store_miss
#print axioms legacy_miss_all
#print axioms starts_of_legacy
end PipeR14.Compat
