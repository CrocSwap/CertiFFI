import SecpMath.CoreCmul
import SecpMath.WordMulAdd
import SecpMath.WideReduce
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
namespace SecpMath.WideWordReduce
open ArmCertValue SecpMath.Product SecpMath.Addition SecpMath.ConstantMultiply
open SecpMath.CoreConstantMultiply

def foldedChain (wide : WideWords) : LimbWords × BitVec 64 :=
  Addition.coreChain4 wide.low (correctionProduct (quotientWord wide))

theorem quotient_computed (wide : WideWords) (bound : wide.value < (limbRadix-1)*modulus) :
    (quotientWord wide).toNat = quotient wide.value := by
  have fit : wide.high.toNat+1 < limbRadix := by
    rw [wide.parts.2]
    exact quotient_fits wide.value bound
  rw [quotientWord_toNat _ fit, wide.parts.2]
  rfl

theorem foldedChain_balance (wide : WideWords) (bound : wide.value < (limbRadix-1)*modulus) :
    (foldedChain wide).1.value+radix*(foldedChain wide).2.toNat = folded wide.value := by
  have chain := Addition.coreChain4_balance wide.low (correctionProduct (quotientWord wide))
  rw [wide.parts.1, correctionProduct_value, quotient_computed wide bound] at chain
  exact chain

private theorem correction_step (d carry total : Nat)
    (hd : d < radix) (hc : carry ≤ 1) (balance : d+radix*carry = folded total)
    (bound : total < (limbRadix-1)*modulus) :
    ((radix-(if carry=0 then correction else 0))+d)%radix = reduceValue total := by
  have range := folded_bounds total bound
  have rpositive : 0 < radix := by decide
  by_cases over : radix ≤ folded total
  · have flag : carry = 1 := by
      simp only [radix] at balance hd over
      omega
    have value : d = folded total-radix := by
      rw [flag] at balance
      simp only [Nat.mul_one] at balance
      omega
    simp only [flag,show ¬ (1:Nat)=0 by decide,↓reduceIte,Nat.sub_zero,
      reduceValue,over,value]
    rw [Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by omega)
  · have flag : carry = 0 := by
      simp only [radix] at balance hd over
      omega
    have value : d = folded total := by
      rw [flag] at balance
      simpa only [Nat.mul_zero,Nat.add_zero] using balance
    have small : correction < radix := correction_lt_radix
    have lower : correction ≤ d := by omega
    have rearrange : radix-correction+d = (d-correction)+radix := by omega
    simp only [flag,↓reduceIte,reduceValue,over]
    rw [rearrange,Nat.add_mod_right]
    have low : d-correction < radix := by omega
    rw [Nat.mod_eq_of_lt low,value]

private theorem zero_mask (flag : BitVec 64) :
    (if flag == 0#64 then correction else 0) =
      if flag.toNat=0 then correction else 0 := by
  by_cases zero : flag = 0#64
  · simp [zero]
  · have nonzero : flag.toNat ≠ 0 := by intro h; exact zero (BitVec.eq_of_toNat_eq h)
    simp [zero,nonzero]

def reduce4 (wide : WideWords) : LimbWords :=
  (SecpMath.coreChain4 (foldedChain wide).1
    (correctionWords ((foldedChain wide).2 == 0#64))).1

theorem reduce4_eq (wide : WideWords) (bound : wide.value < (limbRadix-1)*modulus) :
    (reduce4 wide).value = reduceValue wide.value := by
  have chain := (SecpMath.coreChain4_correct (foldedChain wide).1
    (correctionWords ((foldedChain wide).2 == 0#64))).1
  rw [correctionWords_value,zero_mask] at chain
  exact chain.trans (correction_step _ _ _ (foldedChain wide).1.value_lt
    (Addition.coreChain4_flag ..) (foldedChain_balance wide bound) bound)

theorem reduce4_correct (wide : WideWords) (bound : wide.value < (limbRadix-1)*modulus) :
    (reduce4 wide).value < modulus ∧ (reduce4 wide).value = wide.value%modulus := by
  rw [reduce4_eq wide bound]
  exact reduceValue_correct _ bound

def reduceProduct (low high : LimbWords) : LimbWords :=
  reduce4 (WordMulAdd.mulAdd4 low (BitVec.ofNat 64 correction) high)

theorem reduceProduct_correct (low high : LimbWords) :
    (reduceProduct low high).value < modulus ∧
    (reduceProduct low high).value = (low.value+radix*high.value)%modulus := by
  let total := low.value+radix*high.value
  let first := WordMulAdd.mulAdd4 low (BitVec.ofNat 64 correction) high
  have parts : total%radix = low.value ∧ total/radix = high.value := by
    have small := low.value_lt
    simp only [total,radix] at *
    omega
  have totalBound : total < radix*radix := by
    have hl := low.value_lt
    have hh := high.value_lt
    simp only [total,radix] at *
    omega
  have firstEq : first.value = WideReduction.firstFold total := by
    change (WordMulAdd.mulAdd4 low (BitVec.ofNat 64 correction) high).value = _
    rw [WordMulAdd.mulAdd4_correct]
    unfold WideReduction.firstFold
    rw [parts.1,parts.2]
    rfl
  have firstBound : first.value < (limbRadix-1)*modulus := by
    rw [firstEq]
    exact WideReduction.firstFold_bound total totalBound
  have result := reduce4_correct first firstBound
  rw [firstEq] at result
  exact ⟨result.1,result.2.trans (WideReduction.firstFold_mod total)⟩

#print axioms quotient_computed
#print axioms reduce4_correct
#print axioms reduceProduct_correct
end SecpMath.WideWordReduce
