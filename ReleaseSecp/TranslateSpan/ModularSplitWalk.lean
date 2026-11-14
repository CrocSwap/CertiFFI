-- Generic page normalization includes unsigned address wrap; actual queries remain explicit.
import TranslateSpan.SplitWalk
open Sail ArmFull
open ArmCert.Translate.Model ArmCertWalk S1LogicalReference
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace TranslateSpan.PageSplit.Modular

theorem within_page_nat (start : BitVec 64) (i : Nat)
    (inside : start.toNat % 4096 + i < 4096) :
    (byteVA start i).toNat = start.toNat + i := by
  have top := start.isLt
  have small : i < 2 ^ 64 := by omega
  have bound : start.toNat + i < 2 ^ 64 := by omega
  simp only [byteVA,BitVec.toNat_add,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt bound]

theorem cut_first (start : BitVec 64) (width i : Nat) (hi : i < cut start width) :
    start.toNat % 4096 + i < 4096 := by
  have rem := Nat.mod_lt start.toNat (by decide : 0 < 4096)
  have upper := Nat.min_le_right width (4096 - start.toNat % 4096)
  change cut start width ≤ _ at upper
  omega

theorem cut_second_aligned (start : BitVec 64) (width : Nat) (small : width ≤ 4096)
    (active : cut start width < width) : (byteVA start (cut start width)).toNat % 4096 = 0 := by
  have rem := Nat.mod_lt start.toNat (by decide : 0 < 4096)
  have top := start.isLt
  have edge : cut start width = 4096 - start.toNat % 4096 := by
    simp only [cut] at active ⊢
    omega
  have ci : cut start width < 2 ^ 64 := by omega
  simp only [byteVA,BitVec.toNat_add,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ci,edge]
  omega

theorem byteVA_compose (start : BitVec 64) (offset i : Nat) :
    byteVA start (offset + i) = byteVA (byteVA start offset) i := by
  simp only [byteVA,BitVec.add_assoc,← BitVec.ofNat_add]

theorem second_nat (start : BitVec 64) (width i : Nat) (small : width ≤ 4096)
    (hi : i < width) (second : ¬ i < cut start width) :
    (byteVA start i).toNat = (byteVA start (cut start width)).toNat + (i - cut start width) := by
  have active : cut start width < width := by omega
  have aligned := cut_second_aligned start width small active
  have inside : (byteVA start (cut start width)).toNat % 4096 + (i-cut start width) < 4096 := by omega
  have same : byteVA start i = byteVA (byteVA start (cut start width)) (i-cut start width) := by
    calc
      byteVA start i = byteVA start (cut start width + (i-cut start width)) := congrArg (byteVA start) (by omega)
      _ = _ := byteVA_compose _ _ _
  exact (congrArg BitVec.toNat same).trans (within_page_nat _ _ inside)

/-- Point translations agree with the two actual page anchors, including the
case where the second anchor is zero after unsigned address wrap. -/
theorem point_eq_view {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {state : ArmCertWalk.State} {start : BitVec 64} {width : Nat}
    (small : width ≤ 4096) (image : TopologyImageAt spec state)
    (first : CurrentAt spec config rows mapping state start)
    (second : cut start width < width → CurrentAt spec config rows mapping state (byteVA start (cut start width)))
    (points : ∀ i, i < width → CurrentAt spec config rows mapping state (byteVA start i))
    (i : Nat) (hi : i < width) : mapping (byteVA start i) = view mapping start width i := by
  obtain ⟨qi,di,vi,ci⟩ := points i hi
  by_cases h : i < cut start width
  · obtain ⟨q0,d0,v0,c0⟩ := first
    have geo := cut_first start width i h
    have pos := within_page_nat start i geo
    have eq := access_start_step image d0 di c0 ci i (by rw [vi,v0]; exact pos)
      (by rw [v0]; exact geo)
    simpa only [vi,v0,view,if_pos h] using eq
  · have active : cut start width < width := by omega
    obtain ⟨q1,d1,v1,c1⟩ := second active
    have pos := second_nat start width i small hi h
    have aligned := cut_second_aligned start width small active
    have inside : q1.va.toNat % 4096 + (i-cut start width) < 4096 := by rw [v1,aligned];omega
    have eq := access_start_step image d1 di c1 ci (i-cut start width)
      (by rw [vi,v1]; exact pos) inside
    simpa only [vi,v1,view,if_neg h] using eq

theorem fragment_eq_view {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {state : ArmCertWalk.State} {start : BitVec 64} {width : Nat}
    (small : width ≤ 4096) (image : TopologyImageAt spec state)
    (first : CurrentAt spec config rows mapping state start)
    (second : cut start width < width → CurrentAt spec config rows mapping state (byteVA start (cut start width)))
    (points : ∀ i, i < width → CurrentAt spec config rows mapping state (byteVA start i))
    (q : AccessQuery) (d : S1AccessData spec config rows q)
    (current : CurrentS1AccessAt spec config rows mapping q d state)
    (offset size : Nat) (fits : offset + size ≤ width) (placed : q.va = byteVA start offset)
    (j : Nat) (hj : j < size) (inside : q.va.toNat % 4096 + j < 4096) :
    (mapping q.va).map (· + j) = view mapping start width (offset + j) := by
  have whole : offset+j < width := by omega
  obtain ⟨qb,db,vb,cb⟩ := points (offset+j) whole
  have pos : qb.va.toNat = q.va.toNat + j := by
    rw [vb,byteVA_compose,← placed]
    exact within_page_nat q.va j inside
  have eq := access_start_step image d db current cb j pos inside
  rw [vb,point_eq_view small image first second points _ whole] at eq
  exact eq.symm

#print axioms point_eq_view
#print axioms fragment_eq_view
end TranslateSpan.PageSplit.Modular
