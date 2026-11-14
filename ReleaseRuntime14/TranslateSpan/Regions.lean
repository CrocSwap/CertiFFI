import TranslateSpan.Core
import ArmCertValue.Core
open Sail ArmFull
open ArmCert.Translate.Model ArmCertWalk S1LogicalReference ArmCertValue
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace TranslateSpan

structure Site where
  region : Region
  first : Nat
  size : Nat
  start : BitVec 64

def covers (s : Site) (a : Region × Nat) : Bool :=
  decide (s.region = a.1 ∧ s.first ≤ a.2 ∧ a.2 < s.first + s.size)

def selected (sites : List Site) (a : Region × Nat) : Option Site := sites.find? (fun s => covers s a)

def siteView (sites : List Site) (mapping : BitVec 64 → Option Nat) (r : Region) (j : Nat) : Option Nat :=
  (selected sites (r, j)).bind fun s => (mapping s.start).map (· + (j - s.first))

def siteAnchor (sites : List Site) (a : Region × Nat) : BitVec 64 := ((selected sites a).map Site.start).getD 0

def siteOffset (sites : List Site) (a : Region × Nat) : Nat := a.2 - ((selected sites a).map Site.first).getD 0

theorem selected_mem {sites : List Site} {a : Region × Nat} {s : Site} (h : selected sites a = some s) :
    s ∈ sites ∧ s.region = a.1 ∧ s.first ≤ a.2 ∧ a.2 < s.first + s.size := by
  have m := List.mem_of_find?_eq_some h
  have ok := List.find?_some h
  exact ⟨m, by simpa only [covers, decide_eq_true_eq] using ok⟩

theorem selected_exists {sites : List Site} {a : Region × Nat}
    (cover : ∃ s ∈ sites, covers s a = true) : ∃ s, selected sites a = some s := by
  cases h : selected sites a with
  | some s => exact ⟨s, rfl⟩
  | none =>
    obtain ⟨s, hs, ok⟩ := cover
    exact False.elim ((List.find?_eq_none.1 h) s hs ok)

theorem siteView_eq {sites : List Site} {mapping : BitVec 64 → Option Nat} {a : Region × Nat}
    (cover : ∃ s ∈ sites, covers s a = true) :
    siteView sites mapping a.1 a.2 = anchoredView mapping (siteAnchor sites) (siteOffset sites) a := by
  obtain ⟨s, h⟩ := selected_exists cover
  simp only [siteView, anchoredView, siteAnchor, siteOffset, h, Option.bind_some, Option.map_some,
    Option.getD_some]

/-- Supported source access sizes and their existing size alignment imply both no wrap and page containment. -/
theorem aligned_span (start : BitVec 64) (size : Nat) (supported : size = 1 ∨ size = 4 ∨ size = 8 ∨ size = 16)
    (aligned : start.toNat % size = 0) (i : Nat) (hi : i < size) :
    (start + BitVec.ofNat 64 i).toNat = start.toNat + i ∧ start.toNat % 4096 + i < 4096 := by
  have bound := start.isLt
  rcases supported with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega

/-- A selected covering access has the correct virtual byte and page offset. -/
theorem selected_geometry {sites : List Site} (va : Region → Nat → BitVec 64)
    (geometry : ∀ s ∈ sites, ∀ i, i < s.size →
      (va s.region (s.first + i)).toNat = s.start.toNat + i ∧ s.start.toNat % 4096 + i < 4096)
    {a : Region × Nat} {s : Site} (h : selected sites a = some s) :
    (va a.1 a.2).toNat = s.start.toNat + (a.2 - s.first) ∧ s.start.toNat % 4096 + (a.2 - s.first) < 4096 := by
  obtain ⟨hs, reg, lo, hi⟩ := selected_mem h
  have g := geometry s hs (a.2 - s.first) (by omega)
  rw [reg, show s.first + (a.2 - s.first) = a.2 by omega] at g
  exact g

/-- Every actual access span agrees with the view chosen from the complete access inventory. -/
theorem siteView_span {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {state : ArmCertWalk.State} {sites : List Site}
    (va : Region → Nat → BitVec 64) (image : TopologyImageAt spec state)
    (current : ∀ s ∈ sites, ∃ (q : AccessQuery) (d : S1AccessData spec config rows q),
      q.va = s.start ∧ CurrentS1AccessAt spec config rows mapping q d state)
    (geometry : ∀ s ∈ sites, ∀ i, i < s.size →
      (va s.region (s.first + i)).toNat = s.start.toNat + i ∧ s.start.toNat % 4096 + i < 4096)
    (s : Site) (hs : s ∈ sites) (i : Nat) (hi : i < s.size) :
    siteView sites mapping s.region (s.first + i) = (mapping s.start).map (· + i) := by
  let a : Region × Nat := (s.region, s.first + i)
  have cover : ∃ t ∈ sites, covers t a = true := ⟨s, hs, by simp [covers, a]; omega⟩
  obtain ⟨t, ht⟩ := selected_exists cover
  have mt := (selected_mem ht).1
  obtain ⟨ga, ia⟩ := selected_geometry va geometry ht
  obtain ⟨gb, ib⟩ := geometry s hs i hi
  obtain ⟨qa, da, vqa, ca⟩ := current t mt
  obtain ⟨qb, db, vqb, cb⟩ := current s hs
  have eq := access_spans_agree image da db ca cb (va a.1 a.2) (a.2 - t.first) i
    (by rw [vqa]; exact ga) (by rw [vqb]; exact gb)
    (by rw [vqa]; exact ia) (by rw [vqb]; exact ib)
  simpa only [siteView, show (s.region, s.first + i) = a from rfl, ht, Option.bind_some, vqa, vqb] using eq

/-- Uncovered padding is absent from the physical view; injectivity concerns only selected actual anchors. -/
theorem siteView_injective {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {state : ArmCertWalk.State} {sites : List Site}
    (tracked : List (Region × Nat)) (va : Region → Nat → BitVec 64)
    (virtual : ∀ a ∈ tracked, ∀ b ∈ tracked, a ≠ b → va a.1 a.2 ≠ va b.1 b.2)
    (current : ∀ s ∈ sites, ∃ (q : AccessQuery) (d : S1AccessData spec config rows q),
      q.va = s.start ∧ CurrentS1AccessAt spec config rows mapping q d state)
    (geometry : ∀ s ∈ sites, ∀ i, i < s.size →
      (va s.region (s.first + i)).toNat = s.start.toNat + i ∧ s.start.toNat % 4096 + i < 4096)
    (noDouble : ∀ s ∈ sites, ∀ t ∈ sites, ∀ pa pb,
      mapping s.start = some pa → mapping t.start = some pb → pa / 4096 = pb / 4096 →
      s.start.toNat / 4096 = t.start.toNat / 4096) :
    ∀ a ∈ tracked, ∀ b ∈ tracked, a ≠ b → ∀ pa,
      siteView sites mapping a.1 a.2 = some pa → siteView sites mapping b.1 b.2 ≠ some pa := by
  let active := tracked.filter fun a => (selected sites a).isSome
  have sel : ∀ a ∈ active, ∃ s, selected sites a = some s := by
    intro a ha
    have h := (List.mem_filter.1 ha).2
    exact Option.isSome_iff_exists.1 h
  have active_mem : ∀ a ∈ active, a ∈ tracked := fun a ha => (List.mem_filter.1 ha).1
  have hall := anchored_injective active mapping (fun a => va a.1 a.2) (siteAnchor sites) (siteOffset sites)
    (fun a ha b hb ne => virtual a (active_mem a ha) b (active_mem b hb) ne)
    (by
      intro a ha
      obtain ⟨s, hs⟩ := sel a ha
      obtain ⟨q, d, hq, cur⟩ := current s (selected_mem hs).1
      refine ⟨(d.leafLevel, {paspace := .PAS_NonSecure, address := leafBase d.leafLevel d.view.stable}, d.view.stable.getLsbD 52), ?_⟩
      simp only [siteAnchor, hs, Option.map_some, Option.getD_some]
      rw [← hq, cur.map.mapped]; rfl)
    (by
      intro a ha
      obtain ⟨s, hs⟩ := sel a ha
      simpa only [siteAnchor, siteOffset, hs, Option.map_some, Option.getD_some] using (selected_geometry va geometry hs).1)
    (by
      intro a ha
      obtain ⟨s, hs⟩ := sel a ha
      simpa only [siteAnchor, siteOffset, hs, Option.map_some, Option.getD_some] using (selected_geometry va geometry hs).2)
    (by
      intro a ha b hb pa pb ma mb frame
      obtain ⟨s, hs⟩ := sel a ha
      obtain ⟨t, ht⟩ := sel b hb
      simp only [siteAnchor, hs, ht, Option.map_some, Option.getD_some] at ma mb ⊢
      exact noDouble s (selected_mem hs).1 t (selected_mem ht).1 pa pb ma mb frame)
  intro a ha b hb ne pa hpa hpb
  have aa : a ∈ active := by
    apply List.mem_filter.2; refine ⟨ha, ?_⟩
    cases h : selected sites a with
    | none => simp [siteView, h] at hpa
    | some s => rfl
  have ab : b ∈ active := by
    apply List.mem_filter.2; refine ⟨hb, ?_⟩
    cases h : selected sites b with
    | none => simp [siteView, h] at hpb
    | some s => rfl
  obtain ⟨s, hs⟩ := sel a aa
  obtain ⟨t, ht⟩ := sel b ab
  have ca : ∃ s ∈ sites, covers s a = true := ⟨s, (selected_mem hs).1, List.find?_some (p := fun t => covers t a) hs⟩
  have cb : ∃ s ∈ sites, covers s b = true := ⟨t, (selected_mem ht).1, List.find?_some (p := fun t => covers t b) ht⟩
  rw [siteView_eq ca] at hpa
  rw [siteView_eq cb] at hpb
  exact hall a aa b ab ne pa hpa hpb

/-- Exact physical footprint nonalias policy, without a whole-page restriction. -/
def SpanNonalias (sites : List Site) (mapping : BitVec 64 → Option Nat) : Prop :=
  ∀ s ∈ sites, ∀ t ∈ sites, ∀ i j, i < s.size → j < t.size → ∀ pa pb,
    mapping s.start = some pa → mapping t.start = some pb → pa + i = pb + j →
    s.start.toNat + i = t.start.toNat + j

theorem siteView_injective_of_spans {sites : List Site} {mapping : BitVec 64 → Option Nat}
    (tracked : List (Region × Nat)) (va : Region → Nat → BitVec 64)
    (virtual : ∀ a ∈ tracked, ∀ b ∈ tracked, a ≠ b → va a.1 a.2 ≠ va b.1 b.2)
    (geometry : ∀ s ∈ sites, ∀ i, i < s.size →
      (va s.region (s.first + i)).toNat = s.start.toNat + i ∧ s.start.toNat % 4096 + i < 4096)
    (nonalias : SpanNonalias sites mapping) :
    ∀ a ∈ tracked, ∀ b ∈ tracked, a ≠ b → ∀ pa,
      siteView sites mapping a.1 a.2 = some pa → siteView sites mapping b.1 b.2 ≠ some pa := by
  intro a ha b hb ne pa hpa hpb
  obtain ⟨s, hs, ms⟩ := Option.bind_eq_some_iff.1 hpa
  obtain ⟨t, ht, mt⟩ := Option.bind_eq_some_iff.1 hpb
  obtain ⟨ps, mps, eps⟩ := Option.map_eq_some_iff.1 ms
  obtain ⟨pt, mpt, ept⟩ := Option.map_eq_some_iff.1 mt
  obtain ⟨hsites, rs, ls, us⟩ := selected_mem hs
  obtain ⟨htsites, rt, lt, ut⟩ := selected_mem ht
  have g := nonalias s hsites t htsites (a.2-s.first) (b.2-t.first) (by omega) (by omega)
    ps pt mps mpt (by omega)
  have ga := (selected_geometry va geometry hs).1
  have gb := (selected_geometry va geometry ht).1
  exact virtual a ha b hb ne (BitVec.eq_of_toNat_eq (ga.trans (g.trans gb.symm)))

/-- Transfer a selected site's physical span to the caller's unique region layout. -/
theorem siteView_span_of_layout {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {state : ArmCertWalk.State} {sites : List Site}
    (regions : List Region) (va : Region → Nat → BitVec 64) (image : TopologyImageAt spec state)
    (current : ∀ s ∈ sites, ∃ (q : AccessQuery) (d : S1AccessData spec config rows q),
      q.va = s.start ∧ CurrentS1AccessAt spec config rows mapping q d state)
    (geometry : ∀ s ∈ sites, ∀ i, i < s.size →
      (va s.region (s.first + i)).toNat = s.start.toNat + i ∧ s.start.toNat % 4096 + i < 4096)
    (distinct : ∀ r ∈ regions, ∀ r' ∈ regions, ∀ j j', j < 8*r.words → j' < 8*r'.words →
      va r j = va r' j' → r = r' ∧ j = j')
    (s : Site) (hs : s ∈ sites) (hsr : s.region ∈ regions) (bound : s.first+s.size ≤ 8*s.region.words)
    (r : Region) (hr : r ∈ regions) (j0 n : Nat) (hn : n ≤ s.size) (hw : j0+n ≤ 8*r.words)
    (layout : ∀ t, t < n → va r (j0+t) = s.start + BitVec.ofNat 64 t) :
    ∀ t, t < n → siteView sites mapping r (j0+t) = (mapping s.start).map (· + t) := by
  intro t ht
  have pos : 0 < s.size := by omega
  have g := (geometry s hs 0 pos).1
  simp only [Nat.add_zero] at g
  have z : va s.region s.first = s.start := BitVec.eq_of_toNat_eq g
  have zl := layout 0 (by omega)
  simp at zl
  obtain ⟨rfl, rfl⟩ := distinct r hr s.region hsr j0 s.first (by omega) (by omega) (zl.trans z.symm)
  exact siteView_span va image current geometry s hs t (by omega)

def bytesOf (regions : List Region) : List (Region × Nat) :=
  regions.flatMap fun r => (List.range (8*r.words)).map fun j => (r,j)

theorem bytesOf_mem {regions : List Region} {a : Region × Nat} (ha : a ∈ bytesOf regions) :
    a.1 ∈ regions ∧ a.2 < 8*a.1.words := by
  obtain ⟨r, hr, hm⟩ := List.mem_flatMap.1 ha
  obtain ⟨j, hj, e⟩ := List.mem_map.1 hm
  cases e
  exact ⟨hr, List.mem_range.1 hj⟩

#print axioms siteView_span_of_layout
#print axioms siteView_injective_of_spans
#print axioms siteView_injective
#print axioms siteView_span
#print axioms aligned_span
end TranslateSpan
