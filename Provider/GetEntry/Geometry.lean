import GetEntry.Root
import Walk.S1LogicalTopology
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 100000
namespace S1EntryGeometry

theorem aligned_or_index (base : BitVec 56) (idx : BitVec 9)
    (halign : base.toNat % 4096 = 0) :
    (base ||| (idx +++ 0#3).setWidth 56).toNat = base.toNat + 8 * idx.toNat := by
  have hi := idx.isLt
  have hoff : ((idx +++ 0#3).setWidth 56).toNat = 8 * idx.toNat := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_append, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.zero_mod, Nat.or_zero, Nat.reducePow]
    omega
  rw [BitVec.toNat_or, hoff]
  have hb : base.toNat = 2^12 * (base.toNat / 4096) := by
    have h := Nat.mod_add_div base.toNat 4096
    omega
  conv => lhs; rw [hb]
  rw [← Nat.two_pow_add_eq_or_of_lt (i := 12) (by omega)]
  omega

theorem first_address (base : FullAddress) (va : BitVec 64)
    (halign : base.address.toNat % 4096 = 0)
    (hwidth : base.address.toNat < 2^48) :
    (S1InitialEntryAddress.address va base).address.toNat =
      S1LogicalReference.entryAddress (base.address.setWidth 48) va 0 9 := by
  rw [S1InitialEntryAddress.address, aligned_or_index _ _ halign]
  simp only [S1LogicalReference.entryAddress, S1LogicalReference.entryIndex,
    BitVec.extractLsb', BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hwidth]
#print axioms aligned_or_index
#print axioms first_address
end S1EntryGeometry
