-- Pure P5 arithmetic for the selected subtraction algorithm. This is not a
-- native execution or limb-SSA correspondence theorem.
import Lean.Elab.Tactic.Omega
import Init.Data.BitVec.Lemmas
import Init.Data.Int.DivMod.Lemmas

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000

namespace SecpMath

def radix : Nat := 2 ^ 256
def correction : Nat := 2 ^ 32 + 977
def modulus : Nat := 2 ^ 256 - 2 ^ 32 - 977

theorem radix_split : radix = modulus + correction := by decide
theorem modulus_pos : 0 < modulus := by decide
theorem correction_pos : 0 < correction := by decide
theorem correction_lt_radix : correction < radix := by decide

def subCore (p a b : Nat) : Nat := if b ≤ a then a - b else a + p - b

theorem subCore_lt (p a b : Nat) (ha : a < p) (hb : b < p) : subCore p a b < p := by
  unfold subCore
  split <;> omega

theorem subCore_mod (p a b : Nat) (ha : a < p) (hb : b < p) :
    subCore p a b = (a + p - b) % p := by
  by_cases h : b ≤ a
  · simp only [subCore, if_pos h]
    have hz : a - b < p := by omega
    have he : a + p - b = (a - b) + p := by omega
    rw [he]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hz]
  · simp only [subCore, if_neg h]
    exact (Nat.mod_eq_of_lt (by omega : a + p - b < p)).symm

theorem subCore_int (p a b : Nat) (ha : a < p) (hb : b < p) :
    (subCore p a b : Int) = ((a : Int) - (b : Int)) % (p : Int) := by
  have hz := subCore_lt p a b ha hb
  by_cases h : b ≤ a
  · have hn : subCore p a b = a - b := by simp [subCore, h]
    have hi : (subCore p a b : Int) = (a : Int) - (b : Int) := by rw [hn]; omega
    rw [← hi]
    exact (Int.emod_eq_of_lt (by omega) (by omega)).symm
  · have hn : subCore p a b = a + p - b := by simp [subCore, h]
    have hi : (a : Int) - (b : Int) = (subCore p a b : Int) - (p : Int) := by rw [hn]; omega
    rw [hi, Int.sub_emod_right]
    exact (Int.emod_eq_of_lt (by omega) (by omega)).symm

/-- Whole-word wrap followed by the selected borrow correction. The four-limb
    native-to-whole-word correspondence is a separate P5 obligation. -/
def wrappedSub (r c a b : Nat) : Nat :=
  if b ≤ a then ((r - b) + a) % r
  else ((r - c) + (((r - b) + a) % r)) % r

theorem wrappedSub_eq_core (r c p a b : Nat) (hr : r = p + c)
    (hp : 0 < p) (hc : 0 < c) (ha : a < p) (hb : b < p) :
    wrappedSub r c a b = subCore p a b := by
  by_cases h : b ≤ a
  · simp only [wrappedSub, subCore, if_pos h]
    have hz : a - b < r := by omega
    have he : r - b + a = (a - b) + r := by omega
    rw [he]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hz]
  · simp only [wrappedSub, subCore, if_neg h]
    have hd : r - b + a < r := by omega
    have hz : a + p - b < r := by omega
    rw [Nat.mod_eq_of_lt hd]
    have he : r - c + (r - b + a) = (a + p - b) + r := by omega
    rw [he]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hz]

def subWord (x y : BitVec 256) : BitVec 256 :=
  let d := x - y
  if y.toNat ≤ x.toNat then d else d - BitVec.ofNat 256 correction

theorem subWord_eq_core (x y : BitVec 256) (hx : x.toNat < modulus) (hy : y.toNat < modulus) :
    (subWord x y).toNat = subCore modulus x.toNat y.toNat := by
  have hc : (BitVec.ofNat 256 correction).toNat = correction := by
    exact Nat.mod_eq_of_lt correction_lt_radix
  have hw : (subWord x y).toNat = wrappedSub radix correction x.toNat y.toNat := by
    by_cases h : y.toNat ≤ x.toNat
    · simp only [subWord, wrappedSub, if_pos h, BitVec.toNat_sub]
      rfl
    · simp only [subWord, wrappedSub, if_neg h, BitVec.toNat_sub, hc]
      rfl
  rw [hw]
  exact wrappedSub_eq_core radix correction modulus x.toNat y.toNat
    radix_split modulus_pos correction_pos hx hy

theorem subWord_correct (x y : BitVec 256) (hx : x.toNat < modulus) (hy : y.toNat < modulus) :
    (subWord x y).toNat < modulus ∧
      ((subWord x y).toNat : Int) = ((x.toNat : Int) - (y.toNat : Int)) % (modulus : Int) := by
  rw [subWord_eq_core x y hx hy]
  exact ⟨subCore_lt modulus x.toNat y.toNat hx hy, subCore_int modulus x.toNat y.toNat hx hy⟩

#print axioms radix_split
#print axioms subCore_lt
#print axioms subCore_mod
#print axioms subCore_int
#print axioms wrappedSub_eq_core
#print axioms subWord_eq_core
#print axioms subWord_correct

end SecpMath
