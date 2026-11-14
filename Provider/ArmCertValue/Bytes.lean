-- ArmCert VALUE LAYER: byte decomposition of 64-bit words (pure BitVec/Nat; omega on literal div/mod).
import ArmCertValue.Core
set_option autoImplicit false
namespace ArmCertValue

/-- The zero-extended byte i of v, in place. -/
def byteIn (v : BitVec 64) (i : Nat) : BitVec 64 := ((v >>> (8 * i)).setWidth 8).setWidth 64 <<< (8 * i)

theorem byte_sum (v : BitVec 64) :
    v = byteIn v 0 + byteIn v 1 + byteIn v 2 + byteIn v 3 + byteIn v 4 + byteIn v 5 + byteIn v 6 + byteIn v 7 := by
  apply BitVec.eq_of_toNat_eq
  have hv := v.isLt
  simp only [byteIn, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.reduceMul, Nat.reducePow, Nat.pow_zero, Nat.div_one,
    Nat.mul_one]
  omega

theorem zext_byte' (v : BitVec 64) : (v.setWidth 8).setWidth 64 = v &&& 0xff#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_and,
    show (0xff#64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem bytePart_eq (a : BitVec 64) (k i : Nat) :
    bytePart a k i = ((a >>> (8 * k)).setWidth 8).setWidth 64 <<< (8 * i) := by
  simp only [bytePart, zext_byte']

open HeapV2StepCerts.RegBind (Reg St regVal)

/-- Word/byte coherence of the region model (Memory proves it once from the definitions). -/
def RegionCoherent (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) : Prop :=
  ∀ (s : St) (r : Region) (w : Nat) (v : BitVec 64), regionWord mapping pinv s r w = some v →
    ∀ k, k < 8 → regionByte mapping pinv s r (8 * w + k) = some ((v >>> (8 * k)).setWidth 8)

theorem asm8_eval (vals : List (BitVec 64)) (i0 i1 i2 i3 i4 i5 i6 i7 k0 k1 k2 k3 k4 k5 k6 k7 : Nat)
    (v : BitVec 64)
    (h0 : ((vals.getD i0 0) >>> (8 * k0)).setWidth 8 = (v >>> (8 * 0)).setWidth 8)
    (h1 : ((vals.getD i1 0) >>> (8 * k1)).setWidth 8 = (v >>> (8 * 1)).setWidth 8)
    (h2 : ((vals.getD i2 0) >>> (8 * k2)).setWidth 8 = (v >>> (8 * 2)).setWidth 8)
    (h3 : ((vals.getD i3 0) >>> (8 * k3)).setWidth 8 = (v >>> (8 * 3)).setWidth 8)
    (h4 : ((vals.getD i4 0) >>> (8 * k4)).setWidth 8 = (v >>> (8 * 4)).setWidth 8)
    (h5 : ((vals.getD i5 0) >>> (8 * k5)).setWidth 8 = (v >>> (8 * 5)).setWidth 8)
    (h6 : ((vals.getD i6 0) >>> (8 * k6)).setWidth 8 = (v >>> (8 * 6)).setWidth 8)
    (h7 : ((vals.getD i7 0) >>> (8 * k7)).setWidth 8 = (v >>> (8 * 7)).setWidth 8) :
    Def.eval vals ⟨.asm8 [k0, k1, k2, k3, k4, k5, k6, k7],
      [.id i0, .id i1, .id i2, .id i3, .id i4, .id i5, .id i6, .id i7]⟩ = v := by
  show bytePart (vals.getD i0 0) k0 0 + bytePart (vals.getD i1 0) k1 1 + bytePart (vals.getD i2 0) k2 2 +
    bytePart (vals.getD i3 0) k3 3 + bytePart (vals.getD i4 0) k4 4 + bytePart (vals.getD i5 0) k5 5 +
    bytePart (vals.getD i6 0) k6 6 + bytePart (vals.getD i7 0) k7 7 = v
  show bytePart _ k0 0 + bytePart _ k1 1 + bytePart _ k2 2 + bytePart _ k3 3 + bytePart _ k4 4 +
    bytePart _ k5 5 + bytePart _ k6 6 + bytePart _ k7 7 = v
  rw [bytePart_eq, bytePart_eq, bytePart_eq, bytePart_eq, bytePart_eq, bytePart_eq, bytePart_eq, bytePart_eq,
    h0, h1, h2, h3, h4, h5, h6, h7]
  exact (byte_sum v).symm

theorem byte_sum32 (v : BitVec 64) (h : v.toNat < 2 ^ 32) :
    v = byteIn v 0 + byteIn v 1 + byteIn v 2 + byteIn v 3 := by
  apply BitVec.eq_of_toNat_eq
  simp only [byteIn, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.reduceMul, Nat.reducePow, Nat.pow_zero, Nat.div_one,
    Nat.mul_one]
  omega

theorem asm4_eval (vals : List (BitVec 64)) (i0 i1 i2 i3 k0 k1 k2 k3 : Nat) (v : BitVec 64)
    (hv : v.toNat < 2 ^ 32)
    (h0 : ((vals.getD i0 0) >>> (8 * k0)).setWidth 8 = (v >>> (8 * 0)).setWidth 8)
    (h1 : ((vals.getD i1 0) >>> (8 * k1)).setWidth 8 = (v >>> (8 * 1)).setWidth 8)
    (h2 : ((vals.getD i2 0) >>> (8 * k2)).setWidth 8 = (v >>> (8 * 2)).setWidth 8)
    (h3 : ((vals.getD i3 0) >>> (8 * k3)).setWidth 8 = (v >>> (8 * 3)).setWidth 8) :
    Def.eval vals ⟨.asm4 [k0, k1, k2, k3], [.id i0, .id i1, .id i2, .id i3]⟩ = v := by
  show bytePart (vals.getD i0 0) k0 0 + bytePart (vals.getD i1 0) k1 1 + bytePart (vals.getD i2 0) k2 2 +
    bytePart (vals.getD i3 0) k3 3 = v
  rw [bytePart_eq, bytePart_eq, bytePart_eq, bytePart_eq, h0, h1, h2, h3]
  exact (byte_sum32 v hv).symm

end ArmCertValue
