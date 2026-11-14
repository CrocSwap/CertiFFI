import ArmCertWalk.RootAlignment

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

theorem source_floor_nat_div (value scale : Nat) (positive : 0 < scale) :
    fdiv_int (value : Int) (scale : Int) = ((value / scale : Nat) : Int) := by
  simp [fdiv_int, Int.natCast_tdiv_eq_ediv]
  split
  · omega
  · split
    · omega
    · rfl

theorem align_bits_toNat (value : BitVec 56) (scale : Nat) (positive : 0 < scale) :
    (Align_bits value (scale : Int)).toNat = value.toNat / scale * scale := by
  rw [align_bits_value, source_floor_nat_div value.toNat scale positive]
  have bound : value.toNat / scale * scale < 2^56 :=
    Nat.lt_of_le_of_lt (Nat.div_mul_le_self value.toNat scale) value.isLt
  change (BitVec.ofInt 56 ((value.toNat / scale * scale : Nat) : Int)).toNat = _
  rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt bound

theorem align_bits_mod (value : BitVec 56) (scale : Nat) (positive : 0 < scale) :
    (Align_bits value (scale : Int)).toNat % scale = 0 := by
  rw [align_bits_toNat value scale positive]
  simp

#print axioms source_floor_nat_div
#print axioms align_bits_toNat
#print axioms align_bits_mod

end ArmCertWalk
