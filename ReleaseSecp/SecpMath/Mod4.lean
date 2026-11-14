-- Exact frozen Core single-subtraction reduction for an arbitrary 256-bit input.
import SecpMath.CoreAdd
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
namespace SecpMath.Reduction
open ArmCertValue SecpMath.Addition

#check "CURRENT_DECL adjustedWords"

def adjustedWords (x : LimbWords) : LimbWords :=
  let dd := Op.and.eval [Op.and.eval [x.w1,x.w2],x.w3]
  let carry := Op.carry3.eval [x.w0,BitVec.ofNat 64 correction,0#64]
  let high := Op.add3.eval [dd,0#64,carry]
  ⟨Op.add3.eval [x.w0,BitVec.ofNat 64 correction,0#64],high,high,high⟩

private theorem lowWords_value (word : BitVec 64) :
    (⟨word,0#64,0#64,0#64⟩ : LimbWords).value = word.toNat := by
  change pack4 word.toNat 0 0 0 = word.toNat
  simp only [pack4,Nat.mul_zero,Nat.add_zero]

private theorem numeric_adjustment (a : Nat) (ha : a < limbRadix)
    (ge : limbRadix ≤ a+correction) :
    (a+correction)%limbRadix = pack4 a (limbRadix-1) (limbRadix-1) (limbRadix-1)-modulus := by
  simp only [pack4,limbRadix,correction,modulus] at *
  omega

#check "CURRENT_DECL adjustedWords_over"

theorem adjustedWords_over (x : LimbWords) (over : modulus ≤ x.value) :
    (adjustedWords x).value = x.value-modulus := by
  have bound := (packed_ge_modulus _ _ _ _ x.w0.isLt x.w1.isLt x.w2.isLt x.w3.isLt).mp over
  have k : (BitVec.ofNat 64 correction).toNat = correction := Nat.mod_eq_of_lt (by decide)
  have high1 : x.w1 = ~~~(0#64) := BitVec.eq_of_toNat_eq bound.1
  have high2 : x.w2 = ~~~(0#64) := BitVec.eq_of_toNat_eq bound.2.1
  have high3 : x.w3 = ~~~(0#64) := BitVec.eq_of_toNat_eq bound.2.2.1
  have dd : Op.and.eval [Op.and.eval [x.w1,x.w2],x.w3] = ~~~(0#64) := by
    rw [high1,high2,high3]
    decide
  have lc := carry3_limb x.w0 (BitVec.ofNat 64 correction) 0 (by omega)
  rw [k,limb_carry_flag x.w0.toNat correction 0 x.w0.isLt (by decide) (by omega)] at lc
  simp only [Nat.add_zero,bound.2.2.2,↓reduceIte] at lc
  have carry : Op.carry3.eval [x.w0,BitVec.ofNat 64 correction,0#64] = 1#64 :=
    BitVec.eq_of_toNat_eq lc
  have highZero : Op.add3.eval [~~~(0#64),0#64,1#64] = 0#64 := by decide
  have lo := add3_limb x.w0 (BitVec.ofNat 64 correction) 0 (by omega)
  rw [k] at lo
  have highvalues : x.w1.toNat = limbRadix-1 ∧ x.w2.toNat = limbRadix-1 ∧
      x.w3.toNat = limbRadix-1 := ⟨bound.1,bound.2.1,bound.2.2.1⟩
  have words : adjustedWords x =
      ⟨Op.add3.eval [x.w0,BitVec.ofNat 64 correction,0#64],0#64,0#64,0#64⟩ := by
    dsimp only [adjustedWords]
    rw [dd,carry,highZero]
  have resultValue : (adjustedWords x).value = limbSum x.w0.toNat correction 0 :=
    (congrArg LimbWords.value words).trans ((lowWords_value _).trans lo)
  rw [resultValue]
  change (x.w0.toNat+correction)%limbRadix =
    pack4 x.w0.toNat x.w1.toNat x.w2.toNat x.w3.toNat-modulus
  rw [highvalues.1,highvalues.2.1,highvalues.2.2]
  exact numeric_adjustment x.w0.toNat x.w0.isLt bound.2.2.2

def selectCC (flag original adjusted : BitVec 64) : BitVec 64 :=
  (Op.cselc 3#4).eval [0#64,0#64,flag,0#64,original,adjusted]

theorem selectCC_pure (flag original adjusted : BitVec 64) :
    selectCC flag original adjusted = if flag == 0#64 then original else adjusted := by
  change (if !(flag != 0#64) then original else adjusted) = _
  simp only [bne,Bool.not_not]

def coreReduce4 (x : LimbWords) : LimbWords :=
  let flag := coreComparison x
  let adjusted := adjustedWords x
  ⟨selectCC flag x.w0 adjusted.w0,selectCC flag x.w1 adjusted.w1,
    selectCC flag x.w2 adjusted.w2,selectCC flag x.w3 adjusted.w3⟩

theorem coreReduce4_eq (x : LimbWords) :
    (coreReduce4 x).value = if modulus ≤ x.value then x.value-modulus else x.value := by
  have cmp := coreComparison_correct x
  by_cases over : modulus ≤ x.value
  · simp only [over,↓reduceIte] at cmp ⊢
    have flag : coreComparison x = 1#64 := BitVec.eq_of_toNat_eq cmp
    have words : coreReduce4 x = adjustedWords x := by
      simp only [coreReduce4,flag,selectCC_pure]
      rfl
    rw [words]
    exact adjustedWords_over x over
  · simp only [over,↓reduceIte] at cmp ⊢
    have flag : coreComparison x = 0#64 := BitVec.eq_of_toNat_eq cmp
    have words : coreReduce4 x = x := by
      simp only [coreReduce4,flag,selectCC_pure]
      rfl
    rw [words]

#check "CURRENT_DECL coreReduce4_correct"

theorem coreReduce4_correct (x : LimbWords) :
    (coreReduce4 x).value < modulus ∧ (coreReduce4 x).value = x.value%modulus := by
  have low := x.value_lt
  have twice : radix < modulus+modulus := by decide
  rw [coreReduce4_eq]
  by_cases over : modulus ≤ x.value
  · have reduced : x.value-modulus < modulus := by omega
    have balance : x.value = (x.value-modulus)+modulus := by omega
    simp only [over,↓reduceIte]
    constructor
    · exact reduced
    · calc
        x.value-modulus = ((x.value-modulus)+modulus)%modulus := by
          simp [Nat.mod_eq_of_lt reduced]
        _ = x.value%modulus := congrArg (· % modulus) balance.symm
  · simp only [over,↓reduceIte]
    exact ⟨by omega,(Nat.mod_eq_of_lt (by omega)).symm⟩

#print axioms adjustedWords_over
#print axioms coreReduce4_correct
end SecpMath.Reduction
