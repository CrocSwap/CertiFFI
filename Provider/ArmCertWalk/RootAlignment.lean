import ArmCertWalk.RootGeometry

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk


theorem align_bits_value (value : BitVec 56) (scale : Int) :
    Align_bits value scale = BitVec.ofInt 56 (fdiv_int (value.toNat : Int) scale * scale) := by
  simp [Align_bits, Align_int, Slice_int, Sail.get_slice_int, Sail.BitVec.toNatInt,
    Sail.BitVec.length, Sail.BitVec.castWidth, Sail.Int.toNatChecked]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_zero, BitVec.toNat_ofInt]
  have castMod := Int.toNat_emod
    (x := (fdiv_int (value.toNat : Int) scale * scale) % (2^57 : Int))
    (y := (2^56 : Int)) (Int.emod_nonneg _ (by decide)) (by decide)
  exact castMod.symm.trans (congrArg Int.toNat
    (Int.emod_emod_of_dvd _ (show (2^56 : Int) ∣ (2^57 : Int) from ⟨2, by decide⟩)))

#print axioms align_bits_value

end ArmCertWalk
