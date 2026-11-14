import ArmCertWalk.OutputPermissionMeaning

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

theorem source_permission_bit (descriptor : BitVec 64) (i : Nat) (bound : i < 64) :
    BitVec.setWidth 1 (BitVec.join1 [BitVec.access descriptor i]) =
      BitVec.ofBool (descriptor.getLsbD i) := by
  simp [Sail.BitVec.join1, Sail.BitVec.access, List.map, BitVec.ofBoolListBE,
    getElem!_pos, bound, ← BitVec.getLsbD_eq_getElem]
  cases descriptor.getLsbD i <;> rfl

theorem source_permission_bit_unextended (descriptor : BitVec 64) (i : Nat)
    (bound : i < 64) :
    BitVec.join1 [BitVec.access descriptor i] = BitVec.ofBool (descriptor.getLsbD i) := by
  simpa using source_permission_bit descriptor i bound

theorem append_toNat_add {m n : Nat} (x : BitVec m) (y : BitVec n) :
    (_root_.BitVec.append x y).toNat = x.toNat * 2 ^ n + y.toNat := by
  change (x.toNat <<< n ||| y.toNat) = _
  rw [← Nat.shiftLeft_add_eq_or_of_lt y.isLt x.toNat, Nat.shiftLeft_eq]

theorem source_permission_index (descriptor : BitVec 64) :
    sourcePermissionIndex descriptor = S1LogicalReference.permissionIndex descriptor := by
  unfold sourcePermissionIndex
  rw [source_permission_bit descriptor 51 (by decide), source_permission_bit descriptor 6 (by decide)]
  apply BitVec.eq_of_toNat_eq
  change ((_root_.BitVec.append (_root_.BitVec.append
    (descriptor.extractLsb' 53 2) (BitVec.ofBool (descriptor.getLsbD 51)))
    (BitVec.ofBool (descriptor.getLsbD 6))).toNat) = _
  simp only [S1LogicalReference.permissionIndex, BitVec.toNat_ofNat,
    append_toNat_add]
  have h := (descriptor.extractLsb' 53 2).isLt
  have h1 := (BitVec.ofBool (descriptor.getLsbD 51)).isLt
  have h2 := (BitVec.ofBool (descriptor.getLsbD 6)).isLt
  change ((descriptor.extractLsb' 53 2).toNat * 2 +
    (BitVec.ofBool (descriptor.getLsbD 51)).toNat) * 2 +
    (BitVec.ofBool (descriptor.getLsbD 6)).toNat = _
  omega

theorem permission_nibble_shift (word : BitVec 64) (index : BitVec 4) :
    permissionNibble word index = (word >>> (4 * index.toNat)).setWidth 4 := by
  rfl

#print axioms source_permission_bit
#print axioms source_permission_index
#print axioms permission_nibble_shift

end ArmCertWalk
