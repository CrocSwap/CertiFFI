-- Computed frozen Core product, quotient estimate, fold and final correction.
-- Compiler-table and complete Sail execution joins remain separate.
import SecpMath.Product
import SecpMath.Mod4
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
namespace SecpMath.CoreConstantMultiply
open ArmCertValue SecpMath.Product SecpMath.Addition SecpMath.ConstantMultiply

def quotientWord (wide : WideWords) : BitVec 64 := Op.add.eval [wide.high,1#64]

theorem quotientWord_toNat (wide : WideWords) (fit : wide.high.toNat+1 < limbRadix) :
    (quotientWord wide).toNat = wide.high.toNat+1 := by
  change (wide.high+1#64).toNat = _
  rw [BitVec.toNat_add]
  change (wide.high.toNat+1)%limbRadix = _
  exact Nat.mod_eq_of_lt fit

theorem quotient_computed (c : BitVec 64) (x : LimbWords) (hx : x.value < modulus) :
    (quotientWord (coreMultiplyWord c x)).toNat = quotient (c.toNat*x.value) := by
  have parts := coreMultiplyWord_parts c x
  have fit : (coreMultiplyWord c x).high.toNat+1 < limbRadix := by
    rw [parts.2]
    exact quotient_fits _ (product_bound _ _ c.isLt hx)
  rw [quotientWord_toNat _ fit,parts.2]
  rfl

def correctionProduct (q : BitVec 64) : LimbWords :=
  ⟨Op.mul.eval [q,BitVec.ofNat 64 correction],
    Op.umulh.eval [q,BitVec.ofNat 64 correction],0#64,0#64⟩

private theorem pairValue (low high : BitVec 64) :
    (⟨low,high,0#64,0#64⟩ : LimbWords).value = low.toNat+limbRadix*high.toNat := by
  change pack4 low.toNat high.toNat 0 0 = _
  simp only [pack4,Nat.mul_zero,Nat.add_zero]

theorem correctionProduct_value (q : BitVec 64) :
    (correctionProduct q).value = correction*q.toNat := by
  have product := mul_balance q (BitVec.ofNat 64 correction)
  have k : (BitVec.ofNat 64 correction).toNat = correction := Nat.mod_eq_of_lt (by decide)
  rw [k] at product
  exact (pairValue _ _).trans (product.trans (Nat.mul_comm _ _))

def foldedChain (c : BitVec 64) (x : LimbWords) : LimbWords × BitVec 64 :=
  Addition.coreChain4 (coreMultiplyWord c x).low
    (correctionProduct (quotientWord (coreMultiplyWord c x)))

#check "CURRENT_DECL foldedChain_balance"
theorem foldedChain_balance (c : BitVec 64) (x : LimbWords) (hx : x.value < modulus) :
    (foldedChain c x).1.value+radix*(foldedChain c x).2.toNat = folded (c.toNat*x.value) := by
  have chain := Addition.coreChain4_balance (coreMultiplyWord c x).low
    (correctionProduct (quotientWord (coreMultiplyWord c x)))
  rw [(coreMultiplyWord_parts c x).1,correctionProduct_value,quotient_computed c x hx] at chain
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

def coreCmul4 (c : BitVec 64) (x : LimbWords) : LimbWords :=
  (SecpMath.coreChain4 (foldedChain c x).1
    (correctionWords ((foldedChain c x).2 == 0#64))).1

theorem coreCmul4_eq (c : BitVec 64) (x : LimbWords) (hx : x.value < modulus) :
    (coreCmul4 c x).value = reduceValue (c.toNat*x.value) := by
  have chain := (SecpMath.coreChain4_correct (foldedChain c x).1
    (correctionWords ((foldedChain c x).2 == 0#64))).1
  rw [correctionWords_value,zero_mask] at chain
  exact chain.trans (correction_step _ _ _ (foldedChain c x).1.value_lt
    (Addition.coreChain4_flag ..) (foldedChain_balance c x hx)
    (product_bound _ _ c.isLt hx))

#check "CURRENT_DECL coreCmul4_correct"
theorem coreCmul4_correct (c : BitVec 64) (x : LimbWords) (hx : x.value < modulus) :
    (coreCmul4 c x).value < modulus ∧ (coreCmul4 c x).value = (c.toNat*x.value)%modulus := by
  rw [coreCmul4_eq c x hx]
  exact cmul_reduce_correct _ _ c.isLt hx

#print axioms quotient_computed
#print axioms foldedChain_balance
#print axioms coreCmul4_correct
end SecpMath.CoreConstantMultiply
