-- d199 pipeline: the link from the generated ptr_cNN_k expressions (over the σ0L inputs) to the runtime14 pin
-- VAs (R14E17.pinsOf gpr byte), once per pin form, for Memory's facts_<C> (base register value = pin VA + off).
-- Hypotheses say which inputs hold which entry values (the entry agreement supplies them).
import R14E17.Pins
import ArmCertValue.Core
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace PipeR14
open ArmCertValue

theorem op_add (a b : BitVec 64) : Op.eval .add [a, b] = a + b := rfl
theorem op_lsr (a : BitVec 64) (n : Nat) : Op.eval (.lsr n) [a] = a >>> n := rfl
theorem op_asm8 (a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 64) :
    Op.eval (.asm8 [0, 0, 0, 0, 0, 0, 0, 0]) [a0, a1, a2, a3, a4, a5, a6, a7] =
      bytePart a0 0 0 + bytePart a1 0 1 + bytePart a2 0 2 + bytePart a3 0 3 + bytePart a4 0 4 + bytePart a5 0 5 +
      bytePart a6 0 6 + bytePart a7 0 7 := rfl

/-- Eight entry bytes assembled by the plan's asm8 are the little-endian mem64 read of the pin definition. -/
theorem asm8_mem64 (byte : BitVec 64 → BitVec 8) (a : BitVec 64) (v : Nat → BitVec 64)
    (hv : ∀ t, t < 8 → v t = (byte (a + BitVec.ofNat 64 t)).setWidth 64) :
    Op.eval (.asm8 [0, 0, 0, 0, 0, 0, 0, 0]) [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7] = R14E17.mem64 byte a := by
  have b : ∀ t, t < 8 → (byte (a + BitVec.ofNat 64 t)).toNat < 256 := fun t _ => (byte _).isLt
  rw [op_asm8]
  simp only [bytePart, R14E17.mem64]
  rw [hv 0 (by omega), hv 1 (by omega), hv 2 (by omega), hv 3 (by omega), hv 4 (by omega), hv 5 (by omega),
    hv 6 (by omega), hv 7 (by omega)]
  have b0 := b 0 (by omega); have b1 := b 1 (by omega); have b2 := b 2 (by omega); have b3 := b 3 (by omega)
  have b4 := b 4 (by omega); have b5 := b 5 (by omega); have b6 := b 6 (by omega); have b7 := b 7 (by omega)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_zero, Nat.mul_zero, Nat.shiftLeft_eq]
  generalize (byte (a + 0#64)).toNat = n0 at b0 ⊢
  generalize (byte (a + 1#64)).toNat = n1 at b1 ⊢
  generalize (byte (a + 2#64)).toNat = n2 at b2 ⊢
  generalize (byte (a + 3#64)).toNat = n3 at b3 ⊢
  generalize (byte (a + 4#64)).toNat = n4 at b4 ⊢
  generalize (byte (a + 5#64)).toNat = n5 at b5 ⊢
  generalize (byte (a + 6#64)).toNat = n6 at b6 ⊢
  generalize (byte (a + 7#64)).toNat = n7 at b7 ⊢
  have and255 : ∀ x : Nat, x < 256 → x % 2 ^ 64 &&& 255 % 2 ^ 64 = x := fun x hx => by
    rw [Nat.mod_eq_of_lt (by omega : x < 2 ^ 64), show (255 % 2 ^ 64 : Nat) = 2 ^ 8 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx]
  rw [and255 n0 b0, and255 n1 b1, and255 n2 b2, and255 n3 b3, and255 n4 b4, and255 n5 b5, and255 n6 b6,
    and255 n7 b7]
  simp only [Nat.reducePow, Nat.reduceMul]
  omega

/-- Byte-array index form: x0 + asm8(x1obj bytes 8..15) + 24 = the "x0+mem64[x1+8]+24" pin VA. -/
theorem link_mem64 (gpr : Nat → BitVec 64) (byte : BitVec 64 → BitVec 8) (x0 : BitVec 64) (v : Nat → BitVec 64)
    (hx0 : x0 = gpr 0) (hv : ∀ t, t < 8 → v t = (byte (gpr 1 + 8#64 + BitVec.ofNat 64 t)).setWidth 64) :
    Op.eval .add [x0, Op.eval (.asm8 [0, 0, 0, 0, 0, 0, 0, 0]) [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7]] + 24#64 =
      R14E17.indirectVA gpr byte "x0+mem64[x1+8]+24" := by
  rw [asm8_mem64 byte _ v hv, hx0, op_add]
  simp [R14E17.indirectVA]

/-- Scalar index form: x0 + (x1 >>> 1) + 24 = the "x0+UBFM64[1,63](x1)+24" pin VA. -/
theorem link_ubfm (gpr : Nat → BitVec 64) (byte : BitVec 64 → BitVec 8) (x0 x1 : BitVec 64)
    (hx0 : x0 = gpr 0) (hx1 : x1 = gpr 1) :
    Op.eval .add [x0, Op.eval (.lsr 1) [x1]] + 24#64 = R14E17.indirectVA gpr byte "x0+UBFM64[1,63](x1)+24" := by
  subst hx0 hx1
  rw [op_lsr, op_add]
  simp [R14E17.indirectVA]

/-- Stack form: sp + c (c the plan's constant) is the stack pin (index 31) VA + c. -/
theorem link_sp (sp : BitVec 64) (spPin : Nat) (c : BitVec 64) (hsp : sp = BitVec.ofNat 64 spPin) :
    Op.eval .add [sp, c] = BitVec.ofNat 64 spPin + c := by
  subst hsp; rw [op_add]

/-- The plan's asm8 of a value's own 8 bytes (a stack spill reloaded) is the value. -/
theorem op_asm8_ks (a : BitVec 64) :
    Op.eval (.asm8 [0, 1, 2, 3, 4, 5, 6, 7]) [a, a, a, a, a, a, a, a] =
      bytePart a 0 0 + bytePart a 1 1 + bytePart a 2 2 + bytePart a 3 3 + bytePart a 4 4 + bytePart a 5 5 +
      bytePart a 6 6 + bytePart a 7 7 := rfl

theorem asm8_self (a : BitVec 64) : Op.eval (.asm8 [0, 1, 2, 3, 4, 5, 6, 7]) [a, a, a, a, a, a, a, a] = a := by
  rw [op_asm8_ks]
  apply BitVec.eq_of_toNat_eq
  simp only [bytePart, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have h255 : ∀ x : Nat, x &&& 255 % 2 ^ 64 = x % 256 := fun x => by
    rw [show (255 % 2 ^ 64 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [show (0xff : Nat) = 255 from rfl, h255, Nat.reducePow, Nat.reduceMul]
  have := a.isLt
  omega

#print axioms asm8_self
#print axioms asm8_mem64
#print axioms link_mem64
#print axioms link_ubfm
#print axioms link_sp
end PipeR14
