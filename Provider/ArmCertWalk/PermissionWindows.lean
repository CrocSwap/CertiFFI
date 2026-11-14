import ArmCertWalk.Profile

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

def sourcePermissionNibble (word : BitVec 64) (index : BitVec 4) : BitVec 4 :=
  let bit_index : Int := 4 *i BitVec.toNat index
  Sail.BitVec.castWidth (Sail.BitVec.extractLsb word
    (Sail.Int.toNatChecked (bit_index +i 3)) (Sail.Int.toNatChecked bit_index))

def permissionNibble (word : BitVec 64) (index : BitVec 4) : BitVec 4 :=
  word.extractLsb' (4 * index.toNat) 4

/-- The source cast always has exactly width four; no panic/default value is
used by the pure selected-word view. -/
theorem sourcePermissionNibble_eq (word : BitVec 64) (index : BitVec 4) :
    sourcePermissionNibble word index = permissionNibble word index := by
  have possibilities : index = 0#4 ∨ index = 1#4 ∨ index = 2#4 ∨ index = 3#4 ∨
      index = 4#4 ∨ index = 5#4 ∨ index = 6#4 ∨ index = 7#4 ∨
      index = 8#4 ∨ index = 9#4 ∨ index = 10#4 ∨ index = 11#4 ∨
      index = 12#4 ∨ index = 13#4 ∨ index = 14#4 ∨ index = 15#4 := by
    have bound := index.isLt
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat]
    omega
  rcases possibilities with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem permissionNibble_bound (index : BitVec 4) : 4 * index.toNat + 4 ≤ 64 := by
  have bound := index.isLt
  omega

#print axioms sourcePermissionNibble_eq
#print axioms permissionNibble_bound

end ArmCertWalk
