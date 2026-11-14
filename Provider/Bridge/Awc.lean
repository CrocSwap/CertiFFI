import BridgeDraft.StateProjection
import ArmFull.Fn.M0000
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
namespace ArmBridge.Awc

theorem castWidth_of_eq {a b : Nat} (h : a = b) (x : BitVec a) :
    (Sail.BitVec.castWidth x : BitVec b) = x.cast h := by
  subst h; simp [Sail.BitVec.castWidth]


/-- d193 (certiffi): Lean-core restatement of the AddWithCarry result + NZCV flags (was LNSym's
`_root_.AddWithCarry`). Same theorem names below, now ArmCert/Lean-core only. -/
def lsb1 {n : Nat} (x : BitVec n) (i : Nat) : BitVec 1 := BitVec.extractLsb' i 1 x

structure Flags where
  n : BitVec 1
  z : BitVec 1
  c : BitVec 1
  v : BitVec 1

def awc {n : Nat} (x y : BitVec n) (c : BitVec 1) : BitVec n × Flags :=
  let r := BitVec.setWidth n (BitVec.setWidth (n + 1) x + BitVec.setWidth (n + 1) y + BitVec.setWidth (n + 1) c)
  (r, ⟨lsb1 r (n - 1), if r = BitVec.zero n then 1#1 else 0#1,
    if BitVec.setWidth (n + 1) r = BitVec.setWidth (n + 1) x + BitVec.setWidth (n + 1) y + BitVec.setWidth (n + 1) c
      then 0#1 else 1#1,
    if BitVec.signExtend (n + 1) r = BitVec.signExtend (n + 1) x + BitVec.signExtend (n + 1) y + BitVec.setWidth (n + 1) c
      then 0#1 else 1#1⟩)

/-- The Sail AddWithCarry result, folded. -/
def sres {n : Nat} (x y : BitVec n) (c : BitVec 1) : BitVec n :=
  Sail.BitVec.castWidth (Functions.integer_subrange (↑x.toNat + ↑y.toNat + ↑c.toNat) (↑(Sail.BitVec.length y) - 1) 0)

theorem sres_fold {n : Nat} (x y : BitVec n) (c : BitVec 1) :
    (Sail.BitVec.castWidth (Functions.integer_subrange (↑x.toNat + ↑y.toNat + ↑c.toNat) (↑(Sail.BitVec.length y) - 1) 0) : BitVec n)
      = sres x y c := rfl

theorem sres_toNat {n : Nat} (hn : 0 < n) (x y : BitVec n) (c : BitVec 1) :
    (sres x y c).toNat = (x.toNat + y.toNat + c.toNat) % 2 ^ n := by
  have hw : Sail.Int.toNatChecked ((↑(Sail.BitVec.length y) : Int) - 1 - 0 + 1) = n := by
    simp [Sail.BitVec.length]
  unfold sres Functions.integer_subrange
  rw [castWidth_of_eq hw]
  simp only [BitVec.toNat_cast]
  simp only [Sail.BitVec.castWidth_eq, Sail.get_slice_int]
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, BitVec.toNat_ofInt, hw]
  have h0 : Sail.Int.toNatChecked 0 = 0 := rfl
  simp only [h0, Nat.zero_add, Nat.shiftRight_zero]
  have hpos : (0 : Int) ≤ ↑x.toNat + ↑y.toNat + ↑c.toNat := by omega
  rw [show ((↑x.toNat + ↑y.toNat + ↑c.toNat : Int)) = ((x.toNat + y.toNat + c.toNat : Nat) : Int) by push_cast; rfl]
  rw [show ((2 : Nat) ^ (n + 1) : Nat) = ((2 ^ (n + 1) : Nat)) from rfl]
  rw [← Int.natCast_emod, Int.toNat_natCast]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (Nat.le_succ n))


theorem res_eq {n : Nat} (hn : 0 < n) (x y : BitVec n) (c : BitVec 1) :
    sres x y c = (awc x y c).1 := by
  apply BitVec.eq_of_toNat_eq
  rw [sres_toNat hn]
  have hx := x.isLt; have hy := y.isLt; have hc := c.isLt
  have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
  simp only [awc, BitVec.toNat_setWidth, BitVec.toNat_add, hp]
  rw [Nat.mod_eq_of_lt (a := x.toNat) (by omega), Nat.mod_eq_of_lt (a := y.toNat) (by omega),
    Nat.mod_eq_of_lt (a := c.toNat) (by omega), Nat.mod_eq_of_lt (a := x.toNat + y.toNat) (b := 2 * 2 ^ n) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat + y.toNat + c.toNat) (b := 2 * 2 ^ n) (by omega)]

theorem flagN {n : Nat} (hn : 0 < n) (x y : BitVec n) (c : BitVec 1) :
    BitVec.setWidth 1 (BitVec.join1 [BitVec.access (sres x y c) (Sail.Int.toNatChecked (↑(Sail.BitVec.length y) - 1))])
      = (awc x y c).2.n := by
  have hk : Sail.Int.toNatChecked ((↑(Sail.BitVec.length y) : Int) - 1) = n - 1 := by
    simp only [Sail.BitVec.length]; rw [Sail.Int.toNatChecked_of_nonneg _ (by omega)]; omega
  rw [hk]
  show _ = lsb1 (awc x y c).1 (n - 1)
  rw [← res_eq hn]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have : i = 0 := by omega
  subst this
  simp [BitVec.join1, BitVec.access, lsb1, BitVec.getLsbD_extractLsb', hn]
  rw [BitVec.getElem_ofBoolListBE (by simp)]
  simp only [List.length_map, List.length_cons, List.length_nil, List.map_cons, List.map_nil]
  rw [getElem!_pos (sres x y c) (n - 1) (by omega)]
  simp only [List.getElem_cons_zero, Nat.add_sub_cancel, Nat.sub_zero, BitVec.getElem_ofBool, List.getElem_singleton]
  exact (BitVec.getLsbD_eq_getElem (x := sres x y c) (by omega)).symm

theorem flagZ {n : Nat} (hn : 0 < n) (x y : BitVec n) (c : BitVec 1) :
    (if Functions.IsZero (sres x y c) = true then 1#1 else 0#1) = (awc x y c).2.z := by
  show _ = (if (awc x y c).1 = BitVec.zero n then 1#1 else 0#1)
  rw [← res_eq hn]
  simp only [Functions.IsZero, castWidth_of_eq (rfl : Sail.BitVec.length (sres x y c) = n)]
  by_cases h : sres x y c = BitVec.zero n <;> simp [h]

/-- Arithmetic facts shared by the C/V flag proofs. -/
theorem sum_cases {n : Nat} (x y : BitVec n) (c : BitVec 1) :
    (x.toNat + y.toNat + c.toNat) % 2 ^ n = x.toNat + y.toNat + c.toNat ∨
      (x.toNat + y.toNat + c.toNat) % 2 ^ n + 2 ^ n = x.toNat + y.toNat + c.toNat := by
  have hx := x.isLt; have hy := y.isLt; have hc := c.isLt
  by_cases h : x.toNat + y.toNat + c.toNat < 2 ^ n
  · exact Or.inl (Nat.mod_eq_of_lt h)
  · right
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

theorem flagC {n : Nat} (hn : 0 < n) (x y : BitVec n) (c : BitVec 1) :
    (if (((sres x y c).toNat : Int) == ↑x.toNat + ↑y.toNat + ↑c.toNat) = true then 0#1 else 1#1)
      = (awc x y c).2.c := by
  have hx := x.isLt; have hy := y.isLt; have hc : c.toNat < 2 := c.isLt
  have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
  have hr := sres_toNat hn x y c
  have hs := sum_cases x y c
  show _ = (if BitVec.setWidth (n + 1) (awc x y c).1 =
      BitVec.setWidth (n + 1) x + BitVec.setWidth (n + 1) y + BitVec.setWidth (n + 1) c then 0#1 else 1#1)
  rw [← res_eq hn]
  have m1 : x.toNat % (2 * 2 ^ n) = x.toNat := Nat.mod_eq_of_lt (by omega)
  have m2 : y.toNat % (2 * 2 ^ n) = y.toNat := Nat.mod_eq_of_lt (by omega)
  have m3 : c.toNat % (2 * 2 ^ n) = c.toNat := Nat.mod_eq_of_lt (by omega)
  have m4 : (x.toNat + y.toNat) % (2 * 2 ^ n) = x.toNat + y.toNat := Nat.mod_eq_of_lt (by omega)
  have m5 : (x.toNat + y.toNat + c.toNat) % (2 * 2 ^ n) = x.toNat + y.toNat + c.toNat := Nat.mod_eq_of_lt (by omega)
  have m6 : (sres x y c).toNat % (2 * 2 ^ n) = (sres x y c).toNat := Nat.mod_eq_of_lt (by rw [hr]; have := Nat.mod_lt (x.toNat + y.toNat + c.toNat) (Nat.two_pow_pos n); omega)
  split <;> split <;> first | rfl | (exfalso; simp only [beq_iff_eq, BitVec.toNat_eq, BitVec.toNat_setWidth, BitVec.toNat_add, hp, m1, m2, m3, m4, m5, m6] at *; omega)

theorem flagV {n : Nat} (hn : 0 < n) (x y : BitVec n) (c : BitVec 1) :
    (if ((sres x y c).toInt == x.toInt + y.toInt + ↑c.toNat) = true then 0#1 else 1#1)
      = (awc x y c).2.v := by
  show _ = (if BitVec.signExtend (n + 1) (awc x y c).1 =
      BitVec.signExtend (n + 1) x + BitVec.signExtend (n + 1) y + BitVec.setWidth (n + 1) c then 0#1 else 1#1)
  rw [← res_eq hn]
  have hc : c.toNat < 2 := c.isLt
  have P : (2 : Int) ^ n = 2 * 2 ^ (n - 1) := by
    rw [show n = (n - 1) + 1 by omega, Int.pow_succ]; simp only [Nat.add_sub_cancel]; omega
  have P1 : (2 : Int) ^ (n + 1) = 4 * 2 ^ (n - 1) := by rw [Int.pow_succ, P]; omega
  have Q : (1 : Int) ≤ 2 ^ (n - 1) := by have := Nat.one_le_two_pow (n := n - 1); exact_mod_cast this
  have lx := BitVec.le_toInt x; have ux := BitVec.toInt_lt (x := x)
  have ly := BitVec.le_toInt y; have uy := BitVec.toInt_lt (x := y)
  have e1 : (BitVec.setWidth (n + 1) c).toInt = c.toNat := by
    rw [BitVec.toInt_setWidth]
    apply Int.bmod_eq_of_le_mul_two <;> push_cast <;> omega
  have e2 : (BitVec.signExtend (n + 1) x + BitVec.signExtend (n + 1) y + BitVec.setWidth (n + 1) c).toInt
      = x.toInt + y.toInt + c.toNat := by
    rw [BitVec.toInt_add, BitVec.toInt_add, BitVec.toInt_signExtend_of_le (by omega),
      BitVec.toInt_signExtend_of_le (by omega), e1]
    have b1 : (x.toInt + y.toInt).bmod (2 ^ (n + 1)) = x.toInt + y.toInt :=
      Int.bmod_eq_of_le_mul_two (by push_cast; omega) (by push_cast; omega)
    rw [b1]
    exact Int.bmod_eq_of_le_mul_two (by push_cast; omega) (by push_cast; omega)
  have e3 : (BitVec.signExtend (n + 1) (sres x y c)).toInt = (sres x y c).toInt :=
    BitVec.toInt_signExtend_of_le (by omega)
  have iff : (BitVec.signExtend (n + 1) (sres x y c) =
      BitVec.signExtend (n + 1) x + BitVec.signExtend (n + 1) y + BitVec.setWidth (n + 1) c) ↔
      (sres x y c).toInt = x.toInt + y.toInt + c.toNat := by
    rw [← BitVec.toInt_inj, e2, e3]
  by_cases h : (sres x y c).toInt = x.toInt + y.toInt + c.toNat
  · simp [h, iff.mpr h]
  · simp [h, mt iff.mp h]

theorem isZero_eq {n : Nat} (r : BitVec n) : Functions.IsZero r = decide (r = BitVec.zero n) := by
  unfold Functions.IsZero
  rw [castWidth_of_eq (rfl : Sail.BitVec.length r = n)]
  show (r == BitVec.zero n) = _
  by_cases h : r = 0#n <;> simp [BitVec.zero, h]

theorem zdef {n : Nat} (x y : BitVec n) (c : BitVec 1) :
    (awc x y c).2.z = if (awc x y c).1 = BitVec.zero n then 1#1 else 0#1 := rfl

/-- Fold Bool-conditioned ite (any Decidable instance) into cond, so later rewrites never
leave a stale instance behind. -/
theorem ite_cond {α : Type} (b : Bool) (t e : α) [inst : Decidable (b = true)] :
    @ite α (b = true) inst t e = cond b t e := by
  cases b <;> split <;> simp_all

theorem flagZc {n : Nat} (hn : 0 < n) (x y : BitVec n) (c : BitVec 1) :
    cond (Functions.IsZero (sres x y c)) 1#1 0#1 = (awc x y c).2.z := by
  rw [Bool.cond_eq_ite]; exact flagZ hn x y c
theorem flagCc {n : Nat} (hn : 0 < n) (x y : BitVec n) (c : BitVec 1) :
    cond (((sres x y c).toNat : Int) == ↑x.toNat + ↑y.toNat + ↑c.toNat) 0#1 1#1
      = (awc x y c).2.c := by
  rw [Bool.cond_eq_ite]; exact flagC hn x y c
theorem flagVc {n : Nat} (hn : 0 < n) (x y : BitVec n) (c : BitVec 1) :
    cond ((sres x y c).toInt == x.toInt + y.toInt + ↑c.toNat) 0#1 1#1
      = (awc x y c).2.v := by
  rw [Bool.cond_eq_ite]; exact flagV hn x y c

theorem bv1 (x : BitVec 1) : x = 0#1 ∨ x = 1#1 := by
  rcases x with ⟨⟨v, hv⟩⟩
  rcases (by omega : v = 0 ∨ v = 1) with h | h <;> subst h <;> simp

theorem cat3 (a b c d : BitVec 1) : Sail.BitVec.extractLsb (((a ++ b) ++ c) ++ d) 3 3 = a := by
  rcases bv1 a with rfl | rfl <;> rcases bv1 b with rfl | rfl <;> rcases bv1 c with rfl | rfl <;>
    rcases bv1 d with rfl | rfl <;> decide
theorem cat2 (a b c d : BitVec 1) : Sail.BitVec.extractLsb (((a ++ b) ++ c) ++ d) 2 2 = b := by
  rcases bv1 a with rfl | rfl <;> rcases bv1 b with rfl | rfl <;> rcases bv1 c with rfl | rfl <;>
    rcases bv1 d with rfl | rfl <;> decide
theorem cat1 (a b c d : BitVec 1) : Sail.BitVec.extractLsb (((a ++ b) ++ c) ++ d) 1 1 = c := by
  rcases bv1 a with rfl | rfl <;> rcases bv1 b with rfl | rfl <;> rcases bv1 c with rfl | rfl <;>
    rcases bv1 d with rfl | rfl <;> decide
theorem cat0 (a b c d : BitVec 1) : Sail.BitVec.extractLsb (((a ++ b) ++ c) ++ d) 0 0 = d := by
  rcases bv1 a with rfl | rfl <;> rcases bv1 b with rfl | rfl <;> rcases bv1 c with rfl | rfl <;>
    rcases bv1 d with rfl | rfl <;> decide

#print axioms res_eq
#print axioms flagN
#print axioms flagZ
#print axioms flagC
#print axioms flagV
#print axioms cat3
end ArmBridge.Awc