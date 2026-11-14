-- Pure limb arithmetic; correspondence to the actual compiler SSA is separate.
import SecpMath.Sub

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000

namespace SecpMath

def limbRadix : Nat := 2 ^ 64

def limbDifference (a b borrow : Nat) : Nat :=
  if b + borrow ≤ a then a - (b + borrow) else limbRadix + a - (b + borrow)

def limbBorrow (a b borrow : Nat) : Nat := if b + borrow ≤ a then 0 else 1

theorem limbBorrow_le_one (a b borrow : Nat) : limbBorrow a b borrow ≤ 1 := by
  unfold limbBorrow
  split <;> omega

theorem limbDifference_balance (a b borrow : Nat) (ha : a < limbRadix)
    (hb : b < limbRadix) (hc : borrow ≤ 1) :
    limbDifference a b borrow + b + borrow = a + limbRadix * limbBorrow a b borrow ∧
      limbDifference a b borrow < limbRadix := by
  unfold limbDifference limbBorrow
  split <;> simp only [Nat.mul_zero, Nat.mul_one] <;> omega

def pack4 (a0 a1 a2 a3 : Nat) : Nat :=
  a0 + limbRadix * a1 + limbRadix ^ 2 * a2 + limbRadix ^ 3 * a3

theorem pack4_lt (a0 a1 a2 a3 : Nat) (h0 : a0 < limbRadix) (h1 : a1 < limbRadix)
    (h2 : a2 < limbRadix) (h3 : a3 < limbRadix) : pack4 a0 a1 a2 a3 < radix := by
  simp [pack4, limbRadix, radix] at *
  omega

/-- Telescoping four actual limb balances needs no assumed whole-program result.
    Each balance is supplied by the instruction-local arithmetic correspondence. -/
theorem pack4_balance
    (a0 a1 a2 a3 b0 b1 b2 b3 d0 d1 d2 d3 c1 c2 c3 c4 : Nat)
    (h0 : d0 + b0 = a0 + limbRadix * c1)
    (h1 : d1 + b1 + c1 = a1 + limbRadix * c2)
    (h2 : d2 + b2 + c2 = a2 + limbRadix * c3)
    (h3 : d3 + b3 + c3 = a3 + limbRadix * c4) :
    pack4 d0 d1 d2 d3 + pack4 b0 b1 b2 b3 =
      pack4 a0 a1 a2 a3 + radix * c4 := by
  simp [pack4, limbRadix, radix] at *
  omega

/-- A bounded packed subtraction uniquely identifies both wrap and borrow. -/
theorem packed_difference (a b d borrow : Nat) (_ha : a < radix) (hb : b < radix)
    (hd : d < radix) (hc : borrow ≤ 1) (balance : d + b = a + radix * borrow) :
    borrow = (if b ≤ a then 0 else 1) ∧ d = ((radix - b) + a) % radix := by
  by_cases h : b ≤ a
  · have hc0 : borrow = 0 := by
      by_cases hz : borrow = 0
      · exact hz
      · have : borrow = 1 := by omega
        simp only [this, Nat.mul_one] at balance
        omega
    simp only [h, ↓reduceIte, hc0, Nat.mul_zero, Nat.add_zero] at *
    have he : radix - b + a = (a - b) + radix := by omega
    rw [he]
    simp [Nat.mod_eq_of_lt (show a - b < radix by omega)]
    omega
  · have hc1 : borrow = 1 := by
      by_cases hz : borrow = 0
      · simp only [hz, Nat.mul_zero, Nat.add_zero] at balance
        omega
      · omega
    simp only [h, ↓reduceIte, hc1, Nat.mul_one] at *
    rw [Nat.mod_eq_of_lt (show radix - b + a < radix by omega)]
    constructor
    · trivial
    · omega

/-- The four-limb borrow chain, before the conditional secp256k1 correction. -/
def subtract4 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) : Nat × Nat :=
  let c1 := limbBorrow a0 b0 0
  let c2 := limbBorrow a1 b1 c1
  let c3 := limbBorrow a2 b2 c2
  let c4 := limbBorrow a3 b3 c3
  (pack4 (limbDifference a0 b0 0) (limbDifference a1 b1 c1)
    (limbDifference a2 b2 c2) (limbDifference a3 b3 c3), c4)

theorem subtract4_correct (a0 a1 a2 a3 b0 b1 b2 b3 : Nat)
    (ha0 : a0 < limbRadix) (ha1 : a1 < limbRadix)
    (ha2 : a2 < limbRadix) (ha3 : a3 < limbRadix)
    (hb0 : b0 < limbRadix) (hb1 : b1 < limbRadix)
    (hb2 : b2 < limbRadix) (hb3 : b3 < limbRadix) :
    let result := subtract4 a0 a1 a2 a3 b0 b1 b2 b3
    let a := pack4 a0 a1 a2 a3
    let b := pack4 b0 b1 b2 b3
    result.1 < radix ∧ result.2 = (if b ≤ a then 0 else 1) ∧
      result.1 = ((radix - b) + a) % radix := by
  have h0 := limbDifference_balance a0 b0 0 ha0 hb0 (by omega)
  have h1 := limbDifference_balance a1 b1 (limbBorrow a0 b0 0) ha1 hb1 (limbBorrow_le_one ..)
  have h2 := limbDifference_balance a2 b2 (limbBorrow a1 b1 (limbBorrow a0 b0 0))
    ha2 hb2 (limbBorrow_le_one ..)
  have h3 := limbDifference_balance a3 b3
    (limbBorrow a2 b2 (limbBorrow a1 b1 (limbBorrow a0 b0 0))) ha3 hb3 (limbBorrow_le_one ..)
  have balance := pack4_balance a0 a1 a2 a3 b0 b1 b2 b3 _ _ _ _ _ _ _ _
    (by simpa using h0.1) h1.1 h2.1 h3.1
  have bound := pack4_lt _ _ _ _ h0.2 h1.2 h2.2 h3.2
  have result := packed_difference _ _ _ _ (pack4_lt _ _ _ _ ha0 ha1 ha2 ha3)
    (pack4_lt _ _ _ _ hb0 hb1 hb2 hb3) bound (limbBorrow_le_one ..) balance
  exact ⟨bound, result⟩

/-- Elementary word subtraction, used locally rather than unfolding a run. -/
theorem wordSub_nat (x y : BitVec 64) :
    (x - y).toNat = if y.toNat ≤ x.toNat then x.toNat - y.toNat
      else limbRadix + x.toNat - y.toNat := by
  rw [BitVec.toNat_sub]
  change ((limbRadix - y.toNat) + x.toNat) % limbRadix = _
  have hx : x.toNat < limbRadix := x.isLt
  have hy : y.toNat < limbRadix := y.isLt
  split
  · rename_i h
    have he : limbRadix - y.toNat + x.toNat = (x.toNat - y.toNat) + limbRadix := by omega
    rw [he]
    simp [Nat.mod_eq_of_lt (show x.toNat - y.toNat < limbRadix by omega)]
  · rw [Nat.mod_eq_of_lt (show limbRadix - y.toNat + x.toNat < limbRadix by omega)]
    omega

/-- The low result of an SBC step with a borrow bit, independent of native state.
    Arm carry is the complement of this borrow; that SSA correspondence is separate. -/
theorem wordSub_borrow (x y : BitVec 64) (borrow : Nat) (hc : borrow ≤ 1) :
    (x - y - BitVec.ofNat 64 borrow).toNat = limbDifference x.toNat y.toNat borrow := by
  have hn : (BitVec.ofNat 64 borrow).toNat = borrow :=
    Nat.mod_eq_of_lt (by omega : borrow < 2 ^ 64)
  have hx : x.toNat < limbRadix := x.isLt
  have hy : y.toNat < limbRadix := y.isLt
  simp only [wordSub_nat, hn, limbDifference]
  split <;> split <;> (try split) <;> omega

#print axioms limbDifference_balance
#print axioms pack4_lt
#print axioms pack4_balance
#print axioms packed_difference
#print axioms subtract4_correct
#print axioms wordSub_nat
#print axioms wordSub_borrow

end SecpMath
