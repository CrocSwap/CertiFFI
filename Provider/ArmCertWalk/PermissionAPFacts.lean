import ArmCertWalk.PermissionBitFacts

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

theorem permission_ap_extract (prior : BitVec 3) (bits : BitVec 2) :
    (Sail.BitVec.updateSubrange prior 2 1 bits).extractLsb' 1 2 = bits := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have small : i = 0 ∨ i = 1 := by omega
  rcases small with rfl | rfl <;>
    simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']

theorem permission_ap_dirty (prior : BitVec 3) :
    (BitVec.update prior 2 (Bit 0#1)).extractLsb' 1 2 =
      prior.extractLsb' 1 2 &&& 1#2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have small : i = 0 ∨ i = 1 := by omega
  rcases small with rfl | rfl <;>
    simp [Sail.BitVec.update, Sail.BitVec.updateSubrange', Bit, Sail.BitVec.access]

theorem permission_overlay_index (descriptor : BitVec 64) :
    (0#1 +++ Sail.BitVec.extractLsb descriptor 62 60) =
      (descriptor.extractLsb' 60 3).setWidth 4 := by
  apply BitVec.eq_of_toNat_eq
  change (_root_.BitVec.append (0#1) (descriptor.extractLsb' 60 3)).toNat = _
  rw [append_toNat_add, BitVec.toNat_setWidth_of_le (by decide)]
  simp

#print axioms permission_ap_extract
#print axioms permission_ap_dirty
#print axioms permission_overlay_index

end ArmCertWalk
