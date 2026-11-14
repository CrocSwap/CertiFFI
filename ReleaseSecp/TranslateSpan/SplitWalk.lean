-- Generic page-crossing translation normalization from actual S1 query certificates.
-- This does not rewrite an actual Sail access trace or assert RAM presence/permissions.
import TranslateSpan.Core
open Sail ArmFull
open ArmCert.Translate.Model ArmCertWalk S1LogicalReference
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace TranslateSpan.PageSplit

def byteVA (start : BitVec 64) (i : Nat) : BitVec 64 := start + BitVec.ofNat 64 i
def cut (start : BitVec 64) (width : Nat) : Nat := min width (4096 - start.toNat % 4096)

structure Bounds (start : BitVec 64) (width : Nat) : Prop where
  small : width ≤ 4096
  nowrap : start.toNat + width ≤ 2 ^ 64

theorem byteVA_nat {start : BitVec 64} {width : Nat} (bounds : Bounds start width)
    (i : Nat) (hi : i < width) : (byteVA start i).toNat = start.toNat + i := by
  have ib : i < 2 ^ 64 := by have := bounds.small; omega
  have sb : start.toNat + i < 2 ^ 64 := by have := bounds.nowrap; omega
  simp only [byteVA, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ib, Nat.mod_eq_of_lt sb]

theorem cut_le (start : BitVec 64) (width : Nat) : cut start width ≤ width := Nat.min_le_left _ _

theorem cut_pos (start : BitVec 64) (width : Nat) (positive : 0 < width) : 0 < cut start width := by
  have := Nat.mod_lt start.toNat (by decide : 0 < 4096)
  simp only [cut]
  omega

theorem fragment_geometry {start : BitVec 64} {width : Nat} (bounds : Bounds start width)
    (i : Nat) (hi : i < width) :
    if i < cut start width then start.toNat % 4096 + i < 4096
    else (byteVA start (cut start width)).toNat % 4096 + (i - cut start width) < 4096 := by
  have rem := Nat.mod_lt start.toNat (by decide : 0 < 4096)
  split
  · next first => have := Nat.min_le_right width (4096 - start.toNat % 4096); change cut start width ≤ _ at this; omega
  · next second =>
    have active : cut start width < width := by omega
    have edge : cut start width = 4096 - start.toNat % 4096 := by
      simp only [cut] at active ⊢
      omega
    rw [byteVA_nat bounds _ active, edge]
    have := bounds.small
    omega

/-- Exactly two page anchors suffice for a nonwrapping access of at most one page.
The second anchor is used only when the access actually crosses the first page. -/
def view (mapping : BitVec 64 → Option Nat) (start : BitVec 64) (width i : Nat) : Option Nat :=
  if i < cut start width then (mapping start).map (· + i)
  else (mapping (byteVA start (cut start width))).map (· + (i - cut start width))

/-- Each supplied query is an actual walk certificate at the indicated VA.
No mapping equality for an unchecked interior VA is postulated. -/
def CurrentAt {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (state : ArmCertWalk.State)
    (va : BitVec 64) : Prop :=
  ∃ (q : AccessQuery) (d : S1AccessData spec config rows q),
    q.va = va ∧ CurrentS1AccessAt spec config rows mapping q d state

theorem point_eq_view {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {state : ArmCertWalk.State} {start : BitVec 64} {width : Nat}
    (bounds : Bounds start width) (image : TopologyImageAt spec state)
    (first : CurrentAt spec config rows mapping state start)
    (second : cut start width < width → CurrentAt spec config rows mapping state (byteVA start (cut start width)))
    (points : ∀ i, i < width → CurrentAt spec config rows mapping state (byteVA start i))
    (i : Nat) (hi : i < width) : mapping (byteVA start i) = view mapping start width i := by
  obtain ⟨qi,di,vi,ci⟩ := points i hi
  have pos := byteVA_nat bounds i hi
  have geo := fragment_geometry bounds i hi
  by_cases h : i < cut start width
  · obtain ⟨q0,d0,v0,c0⟩ := first
    have eq := access_start_step image d0 di c0 ci i (by rw [vi,v0]; exact pos)
      (by rw [v0]; simpa only [if_pos h] using geo)
    simpa only [vi,v0,view,if_pos h] using eq
  · have active : cut start width < width := by omega
    obtain ⟨q1,d1,v1,c1⟩ := second active
    have anchor := byteVA_nat bounds (cut start width) active
    have eq := access_start_step image d1 di c1 ci (i - cut start width)
      (by rw [vi,v1,pos,anchor]; omega)
      (by rw [v1]; simpa only [if_neg h] using geo)
    simpa only [vi,v1,view,if_neg h] using eq

/-- An actual native access fragment agrees with the page-normalized point view.
Its query/descriptor, permission evidence and byte ordering remain the native producer's. -/
theorem fragment_eq_view {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {state : ArmCertWalk.State} {start : BitVec 64} {width : Nat}
    (bounds : Bounds start width) (image : TopologyImageAt spec state)
    (first : CurrentAt spec config rows mapping state start)
    (second : cut start width < width → CurrentAt spec config rows mapping state (byteVA start (cut start width)))
    (points : ∀ i, i < width → CurrentAt spec config rows mapping state (byteVA start i))
    (q : AccessQuery) (d : S1AccessData spec config rows q)
    (current : CurrentS1AccessAt spec config rows mapping q d state)
    (offset size : Nat) (fits : offset + size ≤ width) (placed : q.va = byteVA start offset)
    (j : Nat) (hj : j < size) (inside : q.va.toNat % 4096 + j < 4096) :
    (mapping q.va).map (· + j) = view mapping start width (offset + j) := by
  have ho : offset < width := by omega
  have hb : offset + j < width := by omega
  obtain ⟨qb,db,vb,cb⟩ := points (offset + j) hb
  have eq := access_start_step image d db current cb j
    (by rw [vb,placed,byteVA_nat bounds _ ho,byteVA_nat bounds _ hb]; omega) inside
  rw [vb,point_eq_view bounds image first second points _ hb] at eq
  exact eq.symm

#print axioms point_eq_view
#print axioms fragment_eq_view
end TranslateSpan.PageSplit
