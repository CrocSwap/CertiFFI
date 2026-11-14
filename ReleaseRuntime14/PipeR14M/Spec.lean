-- PipeR14.Math.Spec: runtime14 route-kind specifications as pure BitVec functions of the
-- entry inputs, plus their meaning in Lean-runtime terms (lean_box, RC arithmetic, object byte layout).
-- Independent of the P1 plan encoding; the per-case math lemmas (evalDefs D at outs = spec) build on these.
set_option autoImplicit false
namespace PipeR14.Math

/-- Lean scalar boxing: lean_box n = (n <<< 1) ||| 1. -/
def box (n : BitVec 64) : BitVec 64 := (n <<< 1) ||| 1#64
/-- Lean scalar unboxing: lean_unbox x = x >>> 1. -/
def unbox (x : BitVec 64) : BitVec 64 := x >>> 1
/-- Address of byte `i` of a ByteArray object `o` (data starts at offset 24, after header + size + capacity). -/
def byteAddr (o i : BitVec 64) : BitVec 64 := o + i + 24#64
/-- Boxed result of reading byte `b` (ldrb; orr x0, #1, x19, lsl #1). -/
def boxByte (b : BitVec 8) : BitVec 64 := box (b.setWidth 64)
/-- The byte stored by the setter (lsr x8, x2, #1; strb w8). -/
def setByte (v : BitVec 64) : BitVec 8 := (unbox v).setWidth 8
/-- RC word updates (32-bit header RC). -/
def rcDec (rc : BitVec 32) : BitVec 32 := rc - 1#32
def rcInc (rc : BitVec 32) : BitVec 32 := rc + 1#32

theorem box_bit0 (n : BitVec 64) : (n <<< 1) &&& 1#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]
  simp only [BitVec.toNat_ofNat]
  rw [show 1 % 2 ^ 64 = 1 from rfl, Nat.and_one_is_mod]
  omega

theorem box_eq_add (n : BitVec 64) : box n = (n <<< 1) + 1#64 := by
  unfold box
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ (box_bit0 n)]

theorem box_toNat (n : BitVec 64) (h : n.toNat < 2 ^ 63) : (box n).toNat = 2 * n.toNat + 1 := by
  rw [box_eq_add, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]
  simp only [BitVec.toNat_ofNat]
  omega

theorem unbox_box (n : BitVec 64) (h : n.toNat < 2 ^ 63) : unbox (box n) = n := by
  apply BitVec.eq_of_toNat_eq
  unfold unbox
  rw [BitVec.toNat_ushiftRight, box_toNat n h, Nat.shiftRight_eq_div_pow]; omega

theorem boxByte_toNat (b : BitVec 8) : (boxByte b).toNat = 2 * b.toNat + 1 := by
  unfold boxByte
  rw [box_toNat _ (by rw [BitVec.toNat_setWidth]; have := b.isLt; omega), BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by have := b.isLt; omega)]

theorem setByte_toNat (v : BitVec 64) : (setByte v).toNat = (v.toNat / 2) % 256 := by
  unfold setByte unbox
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  all_goals rfl

theorem rcDec_toNat (rc : BitVec 32) (h : 1 ≤ rc.toNat) : (rcDec rc).toNat = rc.toNat - 1 := by
  unfold rcDec; rw [BitVec.toNat_sub]
  all_goals (first | omega | (simp; omega) | simp)

theorem rcInc_toNat (rc : BitVec 32) (h : rc.toNat + 1 < 2 ^ 32) : (rcInc rc).toNat = rc.toNat + 1 := by
  unfold rcInc; rw [BitVec.toNat_add]
  all_goals (first | omega | (simp; omega) | simp)

end PipeR14.Math

#print axioms PipeR14.Math.box_toNat
#print axioms PipeR14.Math.unbox_box
#print axioms PipeR14.Math.rcInc_toNat
#print axioms PipeR14.Math.setByte_toNat
