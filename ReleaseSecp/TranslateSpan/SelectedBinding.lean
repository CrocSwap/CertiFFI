-- Fixed-entry translation facts establish a pure mapping/view span for every selected fragment.
import TranslateSpan.SelectedMap
import ArmCertValue.Physical
import TranslateSpan.ModularSplitWalk
open Sail ArmFull ArmCertWalk ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.SelectedBinding
open ArmCertValue NativeAccess PageSplit

def At (view : Physical.BytePA) (r : Region) (word : Nat)
    (mapping : BitVec 64 → Option Nat) (start : BitVec 64) : Prop :=
  match PairGeometry.selected start with
  | .one16 => ∀ pa, mapping start = some pa → ∀ i, i < 16 → view r (8 * word + i) = some (pa + i)
  | .two8 => ∀ (j : Fin 2) pa, mapping (PairSplit.halfAddress start j) = some pa →
      ∀ i, i < 8 → view r (8 * word + 8 * j.val + i) = some (pa + i)
  | .bytes => ∀ (j : Fin 16) pa, mapping (BitVec.addInt start (j.val : Int)) = some pa →
      view r (8 * word + j.val) = some pa

/-- Point queries occur only at this checked entry; the conclusion is state-free. -/
theorem fragment {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {entry : ArmCertWalk.State} (image : TopologyImageAt spec entry)
    (view : Physical.BytePA) (r : Region) (word : Nat) (start : BitVec 64)
    (points : ∀ t, t < 16 → CurrentAt spec config rows mapping entry (byteVA start t))
    (pointView : ∀ t, t < 16 → view r (8 * word + t) = mapping (byteVA start t))
    (offset i : Nat) (fits : offset + i < 16)
    (inside : (byteVA start offset).toNat % 4096 + i < 4096) :
    view r (8 * word + offset + i) = (mapping (byteVA start offset)).map (· + i) := by
  obtain ⟨qa,da,va,ca⟩ := points offset (by omega)
  obtain ⟨qb,db,vb,cb⟩ := points (offset + i) fits
  have pos : qb.va.toNat = qa.va.toNat + i := by
    rw [vb,PageSplit.Modular.byteVA_compose,← va]
    exact PageSplit.Modular.within_page_nat _ _ (by rwa [va])
  have step := access_start_step image da db ca cb i pos (by rwa [va])
  rw [va,vb] at step
  rw [Nat.add_assoc,pointView _ fits]
  exact step

theorem half_address (start : BitVec 64) (j : Fin 2) :
    PairSplit.halfAddress start j = byteVA start (8 * j.val) := by
  rcases (show j.val = 0 ∨ j.val = 1 by omega) with h | h
  · simp [PairSplit.halfAddress,byteVA,h]
  · simp [PairSplit.halfAddress,byteVA,h,BitVec.addInt]

theorem half_aligned (start : BitVec 64) (aligned : start.toNat % 8 = 0) (j : Fin 2) :
    (byteVA start (8 * j.val)).toNat % 8 = 0 := by
  have bound := start.isLt
  rcases (show j.val = 0 ∨ j.val = 1 by omega) with h | h
  · simpa [byteVA,h] using aligned
  · simp only [byteVA,h,Nat.mul_one,BitVec.toNat_add,BitVec.toNat_ofNat,Nat.reduceMod]
    omega

/-- The selector itself supplies alignment of each actual wide fragment.
There is no alignment or no-wrap restriction on the starting address. -/
theorem at_entry {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {entry : ArmCertWalk.State} (image : TopologyImageAt spec entry)
    (view : Physical.BytePA) (r : Region) (word : Nat) (start : BitVec 64)
    (points : ∀ t, t < 16 → CurrentAt spec config rows mapping entry (byteVA start t))
    (pointView : ∀ t, t < 16 → view r (8 * word + t) = mapping (byteVA start t)) :
    At view r word mapping start := by
  by_cases aligned16 : start.toNat % 16 = 0
  · simp only [At,PairGeometry.selected,if_pos aligned16]
    intro pa mapped i hi
    have inside : start.toNat % 4096 + i < 4096 := by omega
    have span := fragment image view r word start points pointView 0 i (by omega)
      (by simpa [byteVA] using inside)
    simpa only [Nat.add_zero,Nat.zero_add,byteVA,BitVec.add_zero,mapped,Option.map_some] using span
  · by_cases aligned8 : start.toNat % 8 = 0
    · simp only [At,PairGeometry.selected,if_neg aligned16,if_pos aligned8]
      intro j pa mapped i hi
      have aligned := half_aligned start aligned8 j
      have inside : (byteVA start (8 * j.val)).toNat % 4096 + i < 4096 := by omega
      have span := fragment image view r word start points pointView (8 * j.val) i (by omega) inside
      rw [← half_address,mapped,Option.map_some] at span
      exact span
    · simp only [At,PairGeometry.selected,if_neg aligned16,if_neg aligned8]
      intro j pa mapped
      have eq : BitVec.addInt start (j.val : Int) = byteVA start j.val := by
        simp [BitVec.addInt,byteVA]
      rw [pointView j.val j.isLt,← eq,mapped]

#print axioms At
#print axioms fragment
#print axioms half_address
#print axioms half_aligned
#print axioms at_entry
end TranslateSpan.SelectedBinding
