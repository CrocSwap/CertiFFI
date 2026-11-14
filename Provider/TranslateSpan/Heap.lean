import TranslateSpan.Core
import TranslateMem.WalkE17
open Sail ArmFull
open ArmCert.Translate.Model ArmCertWalk S1LogicalReference
open ArmCertValue ArmCertValue.HeapV2Mem TranslateMem
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace TranslateHeapSpan

/-- Actual access anchor for every tracked heap-v2 byte. Input bytes use their own read;
    output/frame bytes use an actual pair access. -/
def anchorSite (a : Region × Nat) : Nat × Nat × Int × Nat × Bool :=
  if a.1 = ArmCertValue.HeapV2Plan.I then (18 + 4 * a.2, 2, (a.2 : Int), 1, false)
  else if a.1 = ArmCertValue.HeapV2Plan.O then (329 + a.2 / 16, 1, (a.2 / 16 * 16 : Nat), 16, true)
  else (if a.2 < 16 then 253 else if a.2 < 32 then 256 else if a.2 < 48 then 353 else 11,
    0, -64 + (a.2 / 16 * 16 : Nat), 16, decide (32 ≤ a.2))

def delta (a : Region × Nat) : Nat := if a.1 = ArmCertValue.HeapV2Plan.I then 0 else a.2 % 16

def anchor (p : HeapV2E17.Pins) (a : Region × Nat) : BitVec 64 := HeapV2E17.dataVA p (anchorSite a)

def bytePA (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (r : Region) (j : Nat) : Option Nat :=
  TranslateSpan.anchoredView mapping (anchor p) delta (r, j)

set_option maxRecDepth 100000 in
/-- Every chosen anchor is a translated start in the existing program inventory. -/
theorem anchors_accessed : heapv2Bytes.all (fun a => HeapV2Plan.symbolicAccesses.contains (anchorSite a)) = true := by
  decide +kernel

theorem anchor_accessed (a : Region × Nat) (ha : a ∈ heapv2Bytes) : anchorSite a ∈ HeapV2Plan.symbolicAccesses := by
  exact List.mem_of_elem_eq_true (List.all_eq_true.1 anchors_accessed a ha)

/-- Existing caller bounds/alignment imply the physical offset remains in the anchor's page. -/
theorem geometry (p : HeapV2E17.Pins) (hd : RegionsDisjoint p)
    (aligned : p.sp % 16 = 0 ∧ p.x0 % 16 = 0 ∧ p.x1 % 16 = 0)
    (a : Region × Nat) (ha : a ∈ heapv2Bytes) :
    (byteVA p a.1 a.2).toNat = (anchor p a).toNat + delta a ∧
    (anchor p a).toNat % 4096 + delta a < 4096 := by
  obtain ⟨h0, h1, hs0, hs1, -, -, -⟩ := hd
  obtain ⟨as0, a0, a1⟩ := aligned
  rcases mem_heapv2Bytes ha with ⟨hr, hj⟩ | ⟨hr, hj⟩ | ⟨hr, hj⟩ <;>
    obtain ⟨r, j⟩ := a <;> simp only at hr hj ⊢ <;> subst r
  all_goals simp [anchor, anchorSite, delta, byteVA, HeapV2E17.dataVA, pinv, HeapV2E17.pin,
    ArmCertValue.HeapV2Plan.I, ArmCertValue.HeapV2Plan.O, ArmCertValue.HeapV2Plan.F,
    BitVec.toNat_ofInt, Int.emod_eq_of_lt] <;> omega

def anchorByte (a : Region × Nat) : Region × Nat :=
  (a.1, if a.1 = ArmCertValue.HeapV2Plan.I then a.2 else a.2 / 16 * 16)

set_option maxRecDepth 100000 in
theorem anchorBytes_tracked : heapv2Bytes.all (fun a => heapv2Bytes.contains (anchorByte a)) = true := by decide +kernel

theorem anchorByte_mem (a : Region × Nat) (ha : a ∈ heapv2Bytes) : anchorByte a ∈ heapv2Bytes :=
  List.mem_of_elem_eq_true (List.all_eq_true.1 anchorBytes_tracked a ha)

theorem anchor_eq (p : HeapV2E17.Pins) (a : Region × Nat) (ha : a ∈ heapv2Bytes) :
    anchor p a = byteVA p (anchorByte a).1 (anchorByte a).2 := by
  rcases mem_heapv2Bytes ha with ⟨hr, hj⟩ | ⟨hr, hj⟩ | ⟨hr, hj⟩ <;>
    obtain ⟨r, j⟩ := a <;> simp only at hr hj ⊢ <;> subst r
  all_goals simp [anchor, anchorSite, anchorByte, byteVA, HeapV2E17.dataVA, pinv, HeapV2E17.pin,
    ArmCertValue.HeapV2Plan.I, ArmCertValue.HeapV2Plan.O, ArmCertValue.HeapV2Plan.F, Int.add_assoc]

/-- Physical RegionsInjective; consumes the existing no-double-mmap deployment policy only at actual anchors. -/
theorem regionsInjective (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat)
    (hd : RegionsDisjoint p) (aligned : p.sp % 16 = 0 ∧ p.x0 % 16 = 0 ∧ p.x1 % 16 = 0)
    (walk : AccessLeaf p mapping) (nd : NoDoubleMapPA p mapping) :
    ∀ a ∈ heapv2Bytes, ∀ b ∈ heapv2Bytes, a ≠ b → ∀ pa,
      bytePA p mapping a.1 a.2 = some pa → bytePA p mapping b.1 b.2 ≠ some pa := by
  apply TranslateSpan.anchored_injective heapv2Bytes mapping (fun a => byteVA p a.1 a.2) (anchor p) delta
  · exact byteVA_injective p hd
  · intro a ha; exact walk (anchorSite a) (anchor_accessed a ha)
  · intro a ha; exact (geometry p hd aligned a ha).1
  · intro a ha; exact (geometry p hd aligned a ha).2
  · intro a ha b hb pa pb ma mb same
    rw [anchor_eq p a ha] at ma
    rw [anchor_eq p b hb] at mb
    have h := nd (anchorByte a) (anchorByte_mem a ha) (anchorByte b) (anchorByte_mem b hb) pa pb ma mb same
    simpa only [pageOf, anchor_eq p a ha, anchor_eq p b hb] using h

/-- Exact current data for each actual access start, extracted from existing E17 closed membership. -/
theorem access_current {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping (HeapV2E17.consumerMap p base mapping table) state)
    (e : Nat × Nat × Int × Nat × Bool) (he : e ∈ HeapV2Plan.symbolicAccesses) :
    ∃ (q : AccessQuery) (data : S1AccessData spec config rows q), q.va = HeapV2E17.dataVA p e ∧
      CurrentS1AccessAt spec config rows mapping q data state := by
  obtain ⟨q, hva, -, -, -, -, data, cur⟩ := closed (HeapV2E17.dataVA p e) (dataAcc e.2.2.2.2) true
    (e.2.2.2.1 : Int) (Or.inl ⟨e, he, rfl, rfl, dataAcc_shape _⟩)
  exact ⟨q, data, hva, cur⟩

def accessLoc (e : Nat × Nat × Int × Nat × Bool) : Region × Nat :=
  let r := if e.2.1 = 0 then ArmCertValue.HeapV2Plan.F
    else if e.2.1 = 1 then ArmCertValue.HeapV2Plan.O else ArmCertValue.HeapV2Plan.I
  (r, (e.2.2.1 - r.off).toNat)

theorem tracked_of_bound (r : Region) (j : Nat) (hr : r ∈ regions) (hj : j < 8 * r.words) :
    (r, j) ∈ heapv2Bytes := by
  exact List.mem_flatMap.2 ⟨r, hr, List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩⟩

/-- All actual spans have the existing region layout and page geometry. -/
theorem access_geometry (p : HeapV2E17.Pins) (hd : RegionsDisjoint p)
    (aligned : p.sp % 16 = 0 ∧ p.x0 % 16 = 0 ∧ p.x1 % 16 = 0)
    (e : Nat × Nat × Int × Nat × Bool) (he : e ∈ HeapV2Plan.symbolicAccesses)
    (i : Nat) (hi : i < e.2.2.2.1) :
    let a := ((accessLoc e).1, (accessLoc e).2 + i)
    a ∈ heapv2Bytes ∧ (byteVA p a.1 a.2).toNat = (HeapV2E17.dataVA p e).toNat + i ∧
      (HeapV2E17.dataVA p e).toNat % 4096 + i < 4096 := by
  have ok := List.all_eq_true.1 accesses_ok e he
  obtain ⟨h0, h1, hs0, hs1, -, -, -⟩ := hd
  obtain ⟨as0, a0, a1⟩ := aligned
  obtain ⟨k, pn, off, size, write⟩ := e
  simp only at hi
  simp only [accessOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  obtain ⟨hr, blk⟩ := ok
  rcases hr with ⟨⟨rfl, lo⟩, top⟩ | ⟨⟨rfl | rfl, lo⟩, top⟩
  all_goals
    dsimp only [accessLoc]
    simp only [ite_true, ite_false, show ¬ (1 : Nat) = 0 by decide, show ¬ (2 : Nat) = 0 by decide,
      show ¬ (2 : Nat) = 1 by decide, ArmCertValue.HeapV2Plan.F, ArmCertValue.HeapV2Plan.O, ArmCertValue.HeapV2Plan.I]
    refine ⟨tracked_of_bound _ _ (by simp [regions, ArmCertValue.HeapV2Plan.regions, ArmCertValue.HeapV2Plan.I,
      ArmCertValue.HeapV2Plan.O, ArmCertValue.HeapV2Plan.F]) (by simp only; omega), ?_⟩
    simp [byteVA, HeapV2E17.dataVA, pinv, HeapV2E17.pin, BitVec.toNat_ofInt]
    omega

/-- Compatibility of the concrete physical byte view with every actual access span. -/
theorem span_compatible {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop} {state : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping (HeapV2E17.consumerMap p base mapping table) state)
    (image : TopologyImageAt spec state) (hd : RegionsDisjoint p)
    (aligned : p.sp % 16 = 0 ∧ p.x0 % 16 = 0 ∧ p.x1 % 16 = 0)
    (e : Nat × Nat × Int × Nat × Bool) (he : e ∈ HeapV2Plan.symbolicAccesses)
    (i : Nat) (hi : i < e.2.2.2.1) :
    bytePA p mapping (accessLoc e).1 ((accessLoc e).2 + i) = (mapping (HeapV2E17.dataVA p e)).map (· + i) := by
  let a : Region × Nat := ((accessLoc e).1, (accessLoc e).2 + i)
  obtain ⟨ha, addb, inb⟩ := access_geometry p hd aligned e he i hi
  obtain ⟨adda, ina⟩ := geometry p hd aligned a ha
  obtain ⟨qa, da, vaa, ca⟩ := access_current closed (anchorSite a) (anchor_accessed a ha)
  obtain ⟨qb, db, vab, cb⟩ := access_current closed e he
  have h := TranslateSpan.access_spans_agree image da db ca cb (byteVA p a.1 a.2) (delta a) i
    (by rw [vaa]; exact adda) (by rw [vab]; exact addb)
    (by rw [vaa]; exact ina) (by rw [vab]; exact inb)
  simpa only [vaa, vab, bytePA, TranslateSpan.anchoredView, anchor, a] using h

#print axioms access_geometry
#print axioms span_compatible
#print axioms regionsInjective
#print axioms access_current
#print axioms anchors_accessed
#print axioms geometry
end TranslateHeapSpan
