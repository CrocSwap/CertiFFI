-- Single-word multiplication reduction arithmetic; compiler/Sail joins separate.
import SecpMath.CoreAdd
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
namespace SecpMath.ConstantMultiply
open ArmCertValue

/-- The word-sized quotient estimate used by cmul. -/
def quotient (total : Nat) : Nat := total/radix+1

def folded (total : Nat) : Nat := total%radix+correction*quotient total

theorem product_bound (c x : Nat) (hc : c < limbRadix) (hx : x < modulus) :
    c*x < (limbRadix-1)*modulus := by
  have bound : c ≤ limbRadix-1 := by omega
  have positive : 0 < limbRadix-1 := by decide
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right x bound)
    (Nat.mul_lt_mul_of_pos_left hx positive)

theorem quotient_fits (total : Nat) (bound : total < (limbRadix-1)*modulus) :
    quotient total < limbRadix := by
  simp only [quotient,limbRadix,modulus,radix] at *
  omega

theorem folded_bounds (total : Nat) (bound : total < (limbRadix-1)*modulus) :
    correction ≤ folded total ∧ folded total < radix+correction*limbRadix := by
  have q := quotient_fits total bound
  have low : total%radix < radix := Nat.mod_lt _ (by decide)
  simp only [folded,quotient,limbRadix,correction,radix] at *
  omega

theorem total_decomposition (total : Nat) :
    (folded total-correction)+modulus*(total/radix) = total := by
  have balance := Nat.mod_add_div total radix
  simp only [folded,quotient,radix,modulus,correction] at *
  omega

def reduceValue (total : Nat) : Nat :=
  if radix ≤ folded total then folded total-radix else folded total-correction

#check "CURRENT_DECL reduceValue_correct"
theorem reduceValue_correct (total : Nat) (bound : total < (limbRadix-1)*modulus) :
    reduceValue total < modulus ∧ reduceValue total = total%modulus := by
  have range := folded_bounds total bound
  have small : correction*limbRadix < modulus := by decide
  have split := radix_split
  have modeq := congrArg (· % modulus) (total_decomposition total)
  simp only [Nat.add_mul_mod_self_left] at modeq
  unfold reduceValue
  by_cases over : radix ≤ folded total
  · simp only [over,↓reduceIte]
    have reduced : folded total-radix < modulus := by omega
    have balance : folded total-correction = (folded total-radix)+modulus := by omega
    have normal : (folded total-correction)%modulus = folded total-radix := by
      rw [balance]
      simp [Nat.mod_eq_of_lt reduced]
    exact ⟨reduced,normal.symm.trans modeq⟩
  · simp only [over,↓reduceIte]
    have reduced : folded total-correction < modulus := by omega
    exact ⟨reduced,(Nat.mod_eq_of_lt reduced).symm.trans modeq⟩

theorem cmul_reduce_correct (c x : Nat) (hc : c < limbRadix) (hx : x < modulus) :
    reduceValue (c*x) < modulus ∧ reduceValue (c*x) = (c*x)%modulus :=
  reduceValue_correct _ (product_bound c x hc hx)

#print axioms quotient_fits
#print axioms reduceValue_correct
#print axioms cmul_reduce_correct
end SecpMath.ConstantMultiply
