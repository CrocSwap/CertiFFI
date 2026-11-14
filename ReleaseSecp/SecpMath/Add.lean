-- Pure addition arithmetic. Actual compiler-row and Sail joins are separate.
import SecpMath.CoreSub

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000

namespace SecpMath.Addition

def limbSum (a b carry : Nat) : Nat := (a+b+carry) % limbRadix
def limbCarry (a b carry : Nat) : Nat := (a+b+carry) / limbRadix

theorem limb_balance (a b carry : Nat) :
    limbSum a b carry + limbRadix * limbCarry a b carry = a+b+carry := by
  exact Nat.mod_add_div _ _

theorem limb_sum_lt (a b carry : Nat) : limbSum a b carry < limbRadix :=
  Nat.mod_lt _ (by decide)

theorem limb_carry_le_one (a b carry : Nat) (ha : a < limbRadix)
    (hb : b < limbRadix) (hc : carry ≤ 1) : limbCarry a b carry ≤ 1 := by
  simp only [limbCarry, limbRadix] at *
  omega

theorem limb_carry_flag (a b carry : Nat) (ha : a < limbRadix)
    (hb : b < limbRadix) (hc : carry ≤ 1) :
    limbCarry a b carry = if limbRadix ≤ a+b+carry then 1 else 0 := by
  simp only [limbCarry, limbRadix] at *
  by_cases over : 2 ^ 64 ≤ a+b+carry <;> simp only [over, ↓reduceIte] <;> omega

theorem packed_balance
    (a0 a1 a2 a3 b0 b1 b2 b3 d0 d1 d2 d3 c1 c2 c3 c4 : Nat)
    (h0 : d0 + limbRadix*c1 = a0+b0)
    (h1 : d1 + limbRadix*c2 = a1+b1+c1)
    (h2 : d2 + limbRadix*c3 = a2+b2+c2)
    (h3 : d3 + limbRadix*c4 = a3+b3+c3) :
    pack4 d0 d1 d2 d3 + radix*c4 = pack4 a0 a1 a2 a3 + pack4 b0 b1 b2 b3 := by
  simp [pack4, limbRadix, radix] at *
  omega

def add4 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) : Nat × Nat :=
  let c1 := limbCarry a0 b0 0
  let c2 := limbCarry a1 b1 c1
  let c3 := limbCarry a2 b2 c2
  let c4 := limbCarry a3 b3 c3
  (pack4 (limbSum a0 b0 0) (limbSum a1 b1 c1)
    (limbSum a2 b2 c2) (limbSum a3 b3 c3), c4)

theorem add4_balance (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) :
    (add4 a0 a1 a2 a3 b0 b1 b2 b3).1 + radix*(add4 a0 a1 a2 a3 b0 b1 b2 b3).2 =
      pack4 a0 a1 a2 a3 + pack4 b0 b1 b2 b3 := by
  apply packed_balance
  · simpa only [Nat.add_zero] using limb_balance a0 b0 0
  · exact limb_balance _ _ _
  · exact limb_balance _ _ _
  · exact limb_balance _ _ _

theorem add4_low_lt (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) :
    (add4 a0 a1 a2 a3 b0 b1 b2 b3).1 < radix :=
  pack4_lt _ _ _ _ (limb_sum_lt ..) (limb_sum_lt ..) (limb_sum_lt ..) (limb_sum_lt ..)

theorem add4_low (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) :
    (add4 a0 a1 a2 a3 b0 b1 b2 b3).1 =
      (pack4 a0 a1 a2 a3 + pack4 b0 b1 b2 b3) % radix := by
  have balance := add4_balance a0 a1 a2 a3 b0 b1 b2 b3
  have low := add4_low_lt a0 a1 a2 a3 b0 b1 b2 b3
  have h := congrArg (· % radix) balance
  simpa only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt low] using h

def addCore (p a b : Nat) : Nat := if p ≤ a+b then a+b-p else a+b

theorem addCore_mod (p a b : Nat) (ha : a < p) (hb : b < p) :
    addCore p a b = (a+b) % p := by
  by_cases over : p ≤ a+b
  · have below : a+b-p < p := by omega
    have balance : a+b = (a+b-p)+p := by omega
    rw [balance]
    simp only [addCore, over, ↓reduceIte]
    simp [Nat.mod_eq_of_lt below]
  · simp only [addCore, over, ↓reduceIte]
    exact (Nat.mod_eq_of_lt (by omega)).symm

def wrappedAdd (a b : Nat) : Nat :=
  ((a+b) % radix + if modulus ≤ a+b then correction else 0) % radix

theorem wrappedAdd_core (a b : Nat) (ha : a < modulus) (hb : b < modulus) :
    wrappedAdd a b = addCore modulus a b := by
  have split := radix_split
  have positive := correction_pos
  by_cases over : modulus ≤ a+b
  · have low : a+b-modulus < radix := by omega
    have balance : a+b+correction = (a+b-modulus)+radix := by omega
    simp only [wrappedAdd, addCore, over, ↓reduceIte]
    rw [Nat.mod_add_mod, balance]
    simp [Nat.mod_eq_of_lt low]
  · have low : a+b < radix := by omega
    simp [wrappedAdd, addCore, over, Nat.mod_eq_of_lt low]

theorem wrappedAdd_correct (a b : Nat) (ha : a < modulus) (hb : b < modulus) :
    wrappedAdd a b < modulus ∧ wrappedAdd a b = (a+b) % modulus := by
  rw [wrappedAdd_core a b ha hb, addCore_mod modulus a b ha hb]
  exact ⟨Nat.mod_lt _ modulus_pos, rfl⟩

/-- The high three limbs must all be maximal for the low word to decide the
    comparison with the pseudo-Mersenne modulus. -/
theorem packed_ge_modulus (d0 d1 d2 d3 : Nat)
    (h0 : d0 < limbRadix) (h1 : d1 < limbRadix)
    (h2 : d2 < limbRadix) (h3 : d3 < limbRadix) :
    modulus ≤ pack4 d0 d1 d2 d3 ↔
      d1 = limbRadix-1 ∧ d2 = limbRadix-1 ∧ d3 = limbRadix-1 ∧
        limbRadix ≤ d0+correction := by
  simp [pack4, limbRadix, modulus, correction] at *
  omega

theorem and3_max (d1 d2 d3 : Nat) (h1 : d1 < limbRadix)
    (h2 : d2 < limbRadix) (h3 : d3 < limbRadix) :
    ((d1 &&& d2) &&& d3) = limbRadix-1 ↔
      d1 = limbRadix-1 ∧ d2 = limbRadix-1 ∧ d3 = limbRadix-1 := by
  constructor
  · intro he
    have h12 : (d1 &&& d2) &&& d3 ≤ d1 &&& d2 := Nat.and_le_left
    have ha : d1 &&& d2 ≤ d1 := Nat.and_le_left
    have hb : d1 &&& d2 ≤ d2 := Nat.and_le_right
    have hc : (d1 &&& d2) &&& d3 ≤ d3 := Nat.and_le_right
    rw [he] at h12 hc
    have positive : 0 < limbRadix := by decide
    omega
  · rintro ⟨rfl,rfl,rfl⟩
    simp

/-- This is the two-instruction condensed comparison used by the assembly. -/
def comparisonCarry (d0 d1 d2 d3 : Nat) : Nat :=
  limbCarry ((d1 &&& d2) &&& d3) 0 (limbCarry d0 correction 0)

theorem comparisonCarry_correct (d0 d1 d2 d3 : Nat)
    (h0 : d0 < limbRadix) (h1 : d1 < limbRadix)
    (h2 : d2 < limbRadix) (h3 : d3 < limbRadix) :
    comparisonCarry d0 d1 d2 d3 =
      if modulus ≤ pack4 d0 d1 d2 d3 then 1 else 0 := by
  have ddBound : ((d1 &&& d2) &&& d3) < limbRadix :=
    Nat.lt_of_le_of_lt Nat.and_le_right h3
  have hc : correction < limbRadix := by decide
  have lowFlag := limb_carry_flag d0 correction 0 h0 hc (by omega)
  have lowBound := limb_carry_le_one d0 correction 0 h0 hc (by omega)
  have highFlag := limb_carry_flag ((d1 &&& d2) &&& d3) 0
    (limbCarry d0 correction 0) ddBound (by decide) lowBound
  have andMax := and3_max d1 d2 d3 h1 h2 h3
  have packed := packed_ge_modulus d0 d1 d2 d3 h0 h1 h2 h3
  unfold comparisonCarry
  rw [highFlag]
  have test : limbRadix ≤ ((d1 &&& d2) &&& d3) + 0 + limbCarry d0 correction 0 ↔
      modulus ≤ pack4 d0 d1 d2 d3 := by
    by_cases low : limbRadix ≤ d0+correction
    · simp only [Nat.add_zero, low, ↓reduceIte] at lowFlag
      rw [lowFlag]
      omega
    · simp only [Nat.add_zero, low, ↓reduceIte] at lowFlag
      rw [lowFlag]
      omega
  simp only [test]

#print axioms packed_balance
#print axioms add4_low
#print axioms wrappedAdd_correct
#print axioms comparisonCarry_correct

end SecpMath.Addition
