import Walk.S1LeafBaseFrame
import ArmCertWalk.PermissionBitFacts

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk


theorem source_cast_toNat {m n : Nat} (word : BitVec m) (width : m = n) :
    (Sail.BitVec.castWidth (m := n) word).toNat = word.toNat := by
  subst n
  rw [Sail.BitVec.castWidth_eq]

theorem source_padded_word (word : BitVec 48) :
    (Sail.BitVec.updateSubrange (0#56) 47 0 word).toNat = word.toNat := by
  have value : Sail.BitVec.updateSubrange (0#56) 47 0 word = word.setWidth 56 := by
    simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
  rw [value, BitVec.toNat_setWidth_of_le (by decide)]

theorem source_leaf_word_toNat (descriptor : BitVec 64) (size : Nat)
    (low : 1 ≤ size) (high : size ≤ 47) :
    (Sail.BitVec.updateSubrange (0#56) 47 0
      (Sail.BitVec.castWidth (m := 48)
        (Sail.BitVec.extractLsb descriptor 47 size +++ (0#size)))).toNat =
      (descriptor.toNat / 2^size % 2^(48-size)) * 2^size := by
  have width : (47 - size + 1) + size = 48 := by omega
  rw [source_padded_word, source_cast_toNat _ width]
  change (_root_.BitVec.append (descriptor.extractLsb' size (47-size+1)) (0#size)).toNat = _
  rw [append_toNat_add]
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.zero_mod, Nat.add_zero]
  rw [show 47-size+1 = 48-size by omega]

theorem leaf_base_native_toNat (descriptor : BitVec 64) (level : Nat) (valid : level ≤ 3) :
    (S1LeafBaseFrame.base descriptor (level : Int)).toNat =
      (descriptor.toNat / 2^(S1LogicalReference.leafBits level) %
        2^(48-S1LogicalReference.leafBits level)) * 2^(S1LogicalReference.leafBits level) := by
  have levels : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by omega
  rcases levels with rfl | rfl | rfl | rfl
  · exact source_leaf_word_toNat descriptor 39 (by decide) (by decide)
  · exact source_leaf_word_toNat descriptor 30 (by decide) (by decide)
  · exact source_leaf_word_toNat descriptor 21 (by decide) (by decide)
  · exact source_leaf_word_toNat descriptor 12 (by decide) (by decide)

theorem leaf_base_value_eq (descriptor : BitVec 64) (level : Nat) (valid : level ≤ 3) :
    S1LeafBaseFrame.base descriptor (level : Int) = S1LogicalReference.leafBase level descriptor := by
  apply BitVec.eq_of_toNat_eq
  rw [leaf_base_native_toNat descriptor level valid]
  change (descriptor.toNat / 2^(S1LogicalReference.leafBits level) %
    2^(48-S1LogicalReference.leafBits level)) * 2^(S1LogicalReference.leafBits level) =
    ((S1LogicalReference.pageBase descriptor).toNat / 2^(S1LogicalReference.leafBits level) *
      2^(S1LogicalReference.leafBits level)) % 2^56
  have levels : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by omega
  rcases levels with rfl | rfl | rfl | rfl
  all_goals simp [S1LogicalReference.leafBase, S1LogicalReference.leafBits,
    S1LogicalReference.pageBase, BitVec.extractLsb', Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  all_goals omega

theorem leaf_base_canonical_total (descriptor : BitVec 64) (level : Nat)
    (state : State) (valid : level ≤ 3) :
    AArch64_LeafBase descriptor 0#1 0#1 .TGx_4KB (level : Int) state =
      .ok (S1LogicalReference.leafBase level descriptor) state := by
  rw [S1LeafBaseFrame.total descriptor (level : Int) state (by omega), leaf_base_value_eq descriptor level valid]

#print axioms source_leaf_word_toNat
#print axioms leaf_base_value_eq
#print axioms leaf_base_canonical_total

end ArmCertWalk
