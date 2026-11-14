import TranslateValue.OpNat

/-! Nat facts for Core v4's byteAt / asm8 (bytePart). -/

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace TranslateValue
open ArmCertValue

/-- Byte k of a natural number. -/
def byteN (a k : Nat) : Nat := (a / 2 ^ (8 * k)) % 256

theorem byteAt_nat (a : BitVec 64) (k : Nat) : (Op.eval (.byteAt k) [a]).toNat = byteN a.toNat k := by
  have e : Op.eval (.byteAt k) [a] = (a >>> (8 * k)) &&& 0xff#64 := rfl
  rw [e, BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have : (0xff#64).toNat = 2 ^ 8 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]; rfl

theorem byteN_lt (a k : Nat) : byteN a k < 256 := Nat.mod_lt _ (by decide)

theorem byteN_zero_small (a : Nat) (h : a < 2 ^ 8) : byteN a 0 = a := by
  simp only [byteN, Nat.mul_zero, Nat.pow_zero, Nat.div_one]; exact Nat.mod_eq_of_lt h

theorem bytePart_nat (a : BitVec 64) (k i : Nat) (hi : i < 8) :
    (bytePart a k i).toNat = byteN a.toNat k * 2 ^ (8 * i) := by
  unfold bytePart
  have hb : ((a >>> (8 * k)) &&& 0xff#64).toNat = byteN a.toNat k := byteAt_nat a k
  rw [BitVec.toNat_shiftLeft, hb, Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  have := byteN_lt a.toNat k
  calc byteN a.toNat k * 2 ^ (8 * i) < 256 * 2 ^ (8 * i) := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
    _ = 2 ^ (8 * i + 8) := by rw [Nat.pow_add, Nat.mul_comm]
    _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)

/-- asm8's value: Σ_i byte_{k_i}(a_i)·2^(8i), with no wraparound. -/
theorem asm8_nat (k0 k1 k2 k3 k4 k5 k6 k7 : Nat) (a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 64) :
    (Op.eval (.asm8 [k0, k1, k2, k3, k4, k5, k6, k7]) [a0, a1, a2, a3, a4, a5, a6, a7]).toNat =
      byteN a0.toNat k0 + byteN a1.toNat k1 * 2 ^ 8 + byteN a2.toNat k2 * 2 ^ 16 + byteN a3.toNat k3 * 2 ^ 24 +
      byteN a4.toNat k4 * 2 ^ 32 + byteN a5.toNat k5 * 2 ^ 40 + byteN a6.toNat k6 * 2 ^ 48 + byteN a7.toNat k7 * 2 ^ 56 := by
  have e : Op.eval (.asm8 [k0, k1, k2, k3, k4, k5, k6, k7]) [a0, a1, a2, a3, a4, a5, a6, a7] =
      bytePart a0 k0 0 + bytePart a1 k1 1 + bytePart a2 k2 2 + bytePart a3 k3 3 +
      bytePart a4 k4 4 + bytePart a5 k5 5 + bytePart a6 k6 6 + bytePart a7 k7 7 := rfl
  have b0 := byteN_lt a0.toNat k0; have b1 := byteN_lt a1.toNat k1; have b2 := byteN_lt a2.toNat k2
  have b3 := byteN_lt a3.toNat k3; have b4 := byteN_lt a4.toNat k4; have b5 := byteN_lt a5.toNat k5
  have b6 := byteN_lt a6.toNat k6; have b7 := byteN_lt a7.toNat k7
  rw [e]
  simp only [BitVec.toNat_add, bytePart_nat _ _ _ (by decide : (0:Nat) < 8), bytePart_nat _ _ _ (by decide : (1:Nat) < 8),
    bytePart_nat _ _ _ (by decide : (2:Nat) < 8), bytePart_nat _ _ _ (by decide : (3:Nat) < 8),
    bytePart_nat _ _ _ (by decide : (4:Nat) < 8), bytePart_nat _ _ _ (by decide : (5:Nat) < 8),
    bytePart_nat _ _ _ (by decide : (6:Nat) < 8), bytePart_nat _ _ _ (by decide : (7:Nat) < 8)]
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.reduceMul, Nat.reducePow]
  omega

/-- The 8 bytes of a 64-bit value reassemble it. -/
theorem bytes_reassemble (a : Nat) (h : a < 2 ^ 64) :
    byteN a 0 + byteN a 1 * 2 ^ 8 + byteN a 2 * 2 ^ 16 + byteN a 3 * 2 ^ 24 + byteN a 4 * 2 ^ 32 +
      byteN a 5 * 2 ^ 40 + byteN a 6 * 2 ^ 48 + byteN a 7 * 2 ^ 56 = a := by
  simp only [byteN, Nat.reduceMul, Nat.reducePow, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  omega

#print axioms asm8_nat
#print axioms bytes_reassemble
end TranslateValue
