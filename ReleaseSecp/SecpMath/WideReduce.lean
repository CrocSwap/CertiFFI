-- Shared pseudo-Mersenne fold and reduction for full multiply/square inputs.
-- This does not assert any algorithm's compiler rows or Sail execution.
import SecpMath.Cmul
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
namespace SecpMath.WideReduction
open SecpMath.ConstantMultiply

def firstFold (total : Nat) : Nat := total%radix+correction*(total/radix)

theorem firstFold_decomposition (total : Nat) :
    firstFold total+modulus*(total/radix) = total := by
  have balance := Nat.mod_add_div total radix
  simp only [firstFold,radix,modulus,correction] at *
  omega

theorem firstFold_mod (total : Nat) : firstFold total%modulus = total%modulus := by
  have equality := congrArg (· % modulus) (firstFold_decomposition total)
  simpa only [Nat.add_mul_mod_self_left] using equality

theorem firstFold_bound (total : Nat) (bound : total < radix*radix) :
    firstFold total < (limbRadix-1)*modulus := by
  have low : total%radix < radix := Nat.mod_lt _ (by decide)
  simp only [firstFold,radix,modulus,correction,limbRadix] at *
  omega

def reduceWide (total : Nat) : Nat := reduceValue (firstFold total)

#check "CURRENT_DECL reduceWide_correct"
theorem reduceWide_correct (total : Nat) (bound : total < radix*radix) :
    reduceWide total < modulus ∧ reduceWide total = total%modulus := by
  have corrected := reduceValue_correct (firstFold total) (firstFold_bound total bound)
  exact ⟨corrected.1,corrected.2.trans (firstFold_mod total)⟩

theorem wide_product_bound (a b : Nat) (ha : a < radix) (hb : b < radix) :
    a*b < radix*radix := by
  have aBound : a ≤ radix-1 := by omega
  have bBound : b ≤ radix-1 := by omega
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul aBound bBound) (by decide)

theorem mul_reduction_correct (a b : Nat) (ha : a < radix) (hb : b < radix) :
    reduceWide (a*b) < modulus ∧ reduceWide (a*b) = (a*b)%modulus :=
  reduceWide_correct _ (wide_product_bound a b ha hb)

theorem sqr_reduction_correct (a : Nat) (ha : a < radix) :
    reduceWide (a*a) < modulus ∧ reduceWide (a*a) = (a*a)%modulus :=
  mul_reduction_correct a a ha ha

#print axioms firstFold_bound
#print axioms reduceWide_correct
#print axioms mul_reduction_correct
#print axioms sqr_reduction_correct
end SecpMath.WideReduction
