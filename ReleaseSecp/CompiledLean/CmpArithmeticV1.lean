import ArmFull.Fn.M0000
import ArmCertValue.Core
open Sail ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 2048
namespace CompiledLean.CmpArithmetic.V1
open ArmCertValue

/-- Exact pure integer-slice expression used by frozen Sail AddWithCarry. -/
def result (x y : BitVec 64) (c : BitVec 1) : BitVec 64 :=
  BitVec.castWidth (m := 64) (integer_subrange
    ((x.toNat : Int) + y.toNat + c.toNat) 63 0)

theorem result_eq (x y : BitVec 64) (c : BitVec 1) :
    result x y c = x + y + c.setWidth 64 := by
  unfold result
  apply BitVec.eq_of_toNat_eq
  simp [Functions.integer_subrange, BitVec.castWidth, Sail.get_slice_int, BitVec.extractLsb',
    BitVec.toNat_ofInt, BitVec.toNat_add, BitVec.toNat_setWidth,
    Sail.Int.toNatChecked, Int.toNatChecked, BitVec.toNat_ofNat]
  omega

theorem full_extract (x : BitVec 64) :
    BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb x (Int.toNatChecked 63) 0) = x := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.castWidth, Sail.BitVec.extractLsb, BitVec.extractLsb, Int.toNatChecked]

theorem bv1 (a : BitVec 1) : a = 0#1 ∨ a = 1#1 := by
  rcases a with ⟨⟨n, hn⟩⟩
  have : n = 0 ∨ n = 1 := by omega
  rcases this with rfl | rfl
  · left; rfl
  · right; rfl

theorem ex4 (a b c d : BitVec 1) :
    Sail.BitVec.extractLsb (BitVec.append (BitVec.append (BitVec.append a b) c) d) 3 3 = a ∧
    Sail.BitVec.extractLsb (BitVec.append (BitVec.append (BitVec.append a b) c) d) 2 2 = b ∧
    Sail.BitVec.extractLsb (BitVec.append (BitVec.append (BitVec.append a b) c) d) 1 1 = c ∧
    Sail.BitVec.extractLsb (BitVec.append (BitVec.append (BitVec.append a b) c) d) 0 0 = d := by
  rcases bv1 a with rfl | rfl <;> rcases bv1 b with rfl | rfl <;>
    rcases bv1 c with rfl | rfl <;> rcases bv1 d with rfl | rfl <;> decide

theorem ex4n (a b c d : BitVec 1) :
    Sail.BitVec.extractLsb (BitVec.append (BitVec.append (BitVec.append a b) c) d) 3 3 = a := (ex4 a b c d).1
theorem ex4z (a b c d : BitVec 1) :
    Sail.BitVec.extractLsb (BitVec.append (BitVec.append (BitVec.append a b) c) d) 2 2 = b := (ex4 a b c d).2.1
theorem ex4c (a b c d : BitVec 1) :
    Sail.BitVec.extractLsb (BitVec.append (BitVec.append (BitVec.append a b) c) d) 1 1 = c := (ex4 a b c d).2.2.1
theorem ex4v (a b c d : BitVec 1) :
    Sail.BitVec.extractLsb (BitVec.append (BitVec.append (BitVec.append a b) c) d) 0 0 = d := (ex4 a b c d).2.2.2

theorem nflag (r : BitVec 64) :
    BitVec.setWidth 1 (BitVec.join1 [BitVec.access r (Int.toNatChecked 63)]) = BitVec.ofBool r.msb := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have : i = 0 := by omega
  subst this
  simp [BitVec.join1, BitVec.access, Int.toNatChecked, BitVec.msb_eq_getLsbD_last]
  rw [getElem!_pos r 63 (by omega)]
  generalize r[63] = b
  cases b <;> rfl

theorem zflag (r : BitVec 64) :
    (if IsZero r = true then 1#1 else 0#1) = if r = 0#64 then 1#1 else 0#1 := by
  simp [IsZero, Sail.BitVec.length, Sail.BitVec.castWidth]

theorem cflag (x y : BitVec 64) (c : BitVec 1) :
    (if (((x + y + c.setWidth 64).toNat : Int) == (x.toNat : Int) + y.toNat + c.toNat) = true
      then 0#1 else 1#1) =
      if 2 ^ 64 ≤ x.toNat + y.toNat + c.toNat then 1#1 else 0#1 := by
  have hc : c.toNat < 2 := c.isLt
  by_cases h : 2 ^ 64 ≤ x.toNat + y.toNat + c.toNat
  · rw [if_pos h, if_neg]; simp [BitVec.toNat_add, BitVec.toNat_setWidth]; omega
  · rw [if_neg h, if_pos]; simp [BitVec.toNat_add, BitVec.toNat_setWidth]; omega

theorem vflag (x y : BitVec 64) (c : BitVec 1) :
    (if ((x + y + c.setWidth 64).toInt == x.toInt + y.toInt + c.toNat) = true then 0#1 else 1#1) =
      if x.toInt + y.toInt + c.toNat < -2 ^ 63 ∨ 2 ^ 63 ≤ x.toInt + y.toInt + c.toNat
      then 1#1 else 0#1 := by
  have hc : c.toNat < 2 := c.isLt
  have ht : (x + y + c.setWidth 64).toInt =
      (x.toInt + y.toInt + (c.toNat : Int)).bmod (2 ^ 64) := by
    rw [BitVec.toInt_add, BitVec.toInt_add, BitVec.toInt_setWidth, Int.bmod_add_bmod, Int.add_bmod_bmod]
  have hx1 := BitVec.le_toInt x
  have hx2 := BitVec.toInt_lt (x := x)
  have hy1 := BitVec.le_toInt y
  have hy2 := BitVec.toInt_lt (x := y)
  rw [ht, Int.bmod_def]
  simp only [beq_iff_eq]
  simp at hx1 hx2 hy1 hy2
  split <;> split <;> split <;> first | rfl | (exfalso; omega)

/-- A pure expression oracle for actual Sail class adapter. -/
def nzcv (x y : BitVec 64) (c : BitVec 1) : BitVec 4 :=
  let r := result x y c
  let n : BitVec 1 := BitVec.setWidth 1 (BitVec.join1 [BitVec.access r (Int.toNatChecked 63)])
  let z : BitVec 1 := if IsZero r = true then 1#1 else 0#1
  let carry : BitVec 1 := if ((r.toNat : Int) == (x.toNat : Int) + y.toNat + c.toNat) = true then 0#1 else 1#1
  let v : BitVec 1 := if (r.toInt == x.toInt + y.toInt + c.toNat) = true then 0#1 else 1#1
  BitVec.append (BitVec.append (BitVec.append n z) carry) v

theorem b01_ofBool (b : Bool) : (BitVec.ofBool b).setWidth 64 = b01 b := by cases b <;> rfl

theorem b01_ite (p : Prop) [Decidable p] :
    (if p then 1#1 else 0#1).setWidth 64 = b01 (decide p) := by
  by_cases h : p <;> simp [h, b01]

theorem flags_to_core (x imm : BitVec 64) :
    ( (Sail.BitVec.extractLsb (nzcv x (~~~imm) 1#1) 3 3).setWidth 64,
      (Sail.BitVec.extractLsb (nzcv x (~~~imm) 1#1) 2 2).setWidth 64,
      (Sail.BitVec.extractLsb (nzcv x (~~~imm) 1#1) 1 1).setWidth 64,
      (Sail.BitVec.extractLsb (nzcv x (~~~imm) 1#1) 0 0).setWidth 64 ) =
    ( Op.sbc3N.eval [x,imm,1#64], Op.sbc3Z.eval [x,imm,1#64],
      Op.sbc3C.eval [x,imm,1#64], Op.sbc3V.eval [x,imm,1#64] ) := by
  unfold nzcv
  dsimp only
  simp only [result_eq, ex4n, ex4z, ex4c, ex4v, nflag, zflag, cflag, vflag,
    b01_ofBool, b01_ite]
  rfl

#print axioms result_eq
#print axioms full_extract
#print axioms flags_to_core
end CompiledLean.CmpArithmetic.V1
