import Bridge.Awc
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
namespace ArmBridge.Mul

/-- The model's integer_subrange at [N-1:0], cast to width N, is BitVec.ofInt N. -/
theorem subrange_ofInt {N : Nat} (hN : 0 < N) (i : Int) :
    (Sail.BitVec.castWidth (Functions.integer_subrange i ((N : Int) - 1) 0) : BitVec N) = BitVec.ofInt N i := by
  have hw : Sail.Int.toNatChecked ((N : Int) - 1 - 0 + 1) = N := by
    rw [Sail.Int.toNatChecked_of_nonneg _ (by omega)]; omega
  unfold Functions.integer_subrange
  rw [ArmBridge.Awc.castWidth_of_eq hw]
  simp only [Sail.BitVec.castWidth_eq, Sail.get_slice_int]
  have h0 : Sail.Int.toNatChecked 0 = 0 := rfl
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_cast, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_ofInt]
  simp only [h0, hw, Nat.zero_add, Nat.shiftRight_zero]
  have p1 : (0 : Int) < ((2 ^ (N + 1) : Nat) : Int) := by have := Nat.two_pow_pos (N + 1); omega
  have p2 : (0 : Int) < ((2 ^ N : Nat) : Int) := by have := Nat.two_pow_pos N; omega
  have e1 := Int.emod_nonneg i (Int.ne_of_gt p1)
  have := Int.toNat_emod e1 (Int.le_of_lt p2)
  rw [Int.toNat_natCast] at this
  rw [← this]
  congr 1
  have hd : ((2 ^ N : Nat) : Int) ∣ ((2 ^ (N + 1) : Nat) : Int) := by
    exact Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 (Nat.le_succ N))
  exact Int.emod_emod_of_dvd i hd

theorem madd_ofInt {N : Nat} (a x y : BitVec N) :
    BitVec.ofInt N ((a.toNat : Int) + (x.toNat : Int) * (y.toNat : Int)) = a + x * y := by
  rw [BitVec.ofInt_add, BitVec.ofInt_mul]
  simp only [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem msub_ofInt {N : Nat} (a x y : BitVec N) :
    BitVec.ofInt N ((a.toNat : Int) - (x.toNat : Int) * (y.toNat : Int)) = a - x * y := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.ofInt_mul]
  simp only [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact (BitVec.sub_eq_add_neg _ _).symm

/-- integer_subrange i 127 64 (UMULH/SMULH high half). -/
theorem subrange_hi (i : Int) :
    (Sail.BitVec.castWidth (Functions.integer_subrange i 127 64) : BitVec 64) =
      BitVec.extractLsb' 64 64 (BitVec.ofInt 128 i) := by
  unfold Functions.integer_subrange
  simp only [Sail.get_slice_int]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
  rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_extractLsb']
  simp only [BitVec.getLsbD, BitVec.toNat_ofInt]
  simp [Sail.Int.toNatChecked, hj]
  have e1 : 0 ≤ i % (680564733841876926926749214863536422912 : Int) := Int.emod_nonneg i (by decide)
  have hd : (340282366920938463463374607431768211456 : Int) ∣ 680564733841876926926749214863536422912 := by decide
  rw [← Int.emod_emod_of_dvd i hd, Int.toNat_emod e1 (by decide),
    show (340282366920938463463374607431768211456 : Int).toNat = 2 ^ 128 from rfl, Nat.testBit_mod_two_pow]
  have : 64 + j < 128 := by omega
  simp [this]

theorem umul_ofInt (x y : BitVec 64) :
    BitVec.ofInt 128 ((x.toNat : Int) * (y.toNat : Int)) = BitVec.setWidth 128 x * BitVec.setWidth 128 y := by
  rw [BitVec.ofInt_mul]
  simp only [BitVec.ofInt_natCast, BitVec.ofNat_toNat]

theorem smul_ofInt (x y : BitVec 64) :
    BitVec.ofInt 128 (x.toInt * y.toInt) = BitVec.signExtend 128 x * BitVec.signExtend 128 y := by
  rw [BitVec.ofInt_mul]
  rfl

theorem zext_subrange_hi (i : Int) :
    BitVec.zeroExtend 64 (Functions.integer_subrange i 127 64) = BitVec.extractLsb' 64 64 (BitVec.ofInt 128 i) := by
  rw [← subrange_hi i]
  rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_cast, hj]

theorem umulh_val (x y : BitVec 64) :
    BitVec.zeroExtend 64 (Functions.integer_subrange ((x.toNat : Int) * (y.toNat : Int)) 127 64) =
      BitVec.extractLsb' 64 64 (BitVec.setWidth 128 x * BitVec.setWidth 128 y) := by
  rw [zext_subrange_hi, umul_ofInt]

theorem smulh_val (x y : BitVec 64) :
    BitVec.zeroExtend 64 (Functions.integer_subrange (x.toInt * y.toInt) 127 64) =
      BitVec.extractLsb' 64 64 (BitVec.signExtend 128 x * BitVec.signExtend 128 y) := by
  rw [zext_subrange_hi, smul_ofInt]

#print axioms umulh_val
#print axioms smulh_val
#print axioms subrange_ofInt
#print axioms madd_ofInt
#print axioms msub_ofInt
#print axioms subrange_hi
#print axioms umul_ofInt
#print axioms smul_ofInt
end ArmBridge.Mul
