import ArmCertWalk.RootEntryFacts
import ArmCertWalk.PermissionBitFacts

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

theorem checked_toNat_nonnegative (value : Int) (nonnegative : 0 ≤ value) :
    Sail.Int.toNatChecked value = value.toNat := by
  cases value <;> simp_all [Sail.Int.toNatChecked]

def rootEntryIndex (params : S1TTWParams) (level : Int) (va : BitVec 64) : BitVec 56 :=
  Sail.BitVec.zeroExtend
    (Sail.BitVec.extractLsb va (Sail.Int.toNatChecked (rootEntryHigh params))
      (Sail.Int.toNatChecked (rootEntryLow level)) +++ Zeros (n := 3)) 56

theorem root_entry_value_eq (params : S1TTWParams) (level : Int) (va : BitVec 64)
    (base : FullAddress) :
    rootEntryValue params level va base =
      { paspace := base.paspace, address := base.address ||| rootEntryIndex params level va } := by
  rfl

theorem root_entry_index_toNat (params : S1TTWParams) (level : Int) (va : BitVec 64)
    (bounds : RootEntryBounds params level) :
    (rootEntryIndex params level va).toNat =
      8 * (va.toNat / 2 ^ (rootEntryLow level).toNat %
        2 ^ ((rootEntryHigh params).toNat - (rootEntryLow level).toNat + 1)) := by
  rcases bounds with ⟨low, ordered, high, width⟩
  have highNonnegative : 0 ≤ rootEntryHigh params := by omega
  have nativeWidth : (rootEntryHigh params).toNat - (rootEntryLow level).toNat + 1 + 3 ≤ 56 := by
    omega
  unfold rootEntryIndex
  rw [checked_toNat_nonnegative _ highNonnegative, checked_toNat_nonnegative _ low]
  change (BitVec.setWidth 56 (_root_.BitVec.append
    (va.extractLsb' (rootEntryLow level).toNat
      ((rootEntryHigh params).toNat - (rootEntryLow level).toNat + 1)) (0#3))).toNat = _
  rw [BitVec.toNat_setWidth_of_le nativeWidth, append_toNat_add]
  simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow, Nat.mul_comm]

#print axioms checked_toNat_nonnegative
#print axioms root_entry_value_eq
#print axioms root_entry_index_toNat

end ArmCertWalk
