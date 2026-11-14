-- Exact frozen Core negation arithmetic; compiler rows and Sail are separate.
import SecpMath.CoreSub
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
namespace SecpMath.Negation
open ArmCertValue

theorem orrShl_zero (x y : BitVec 64) : (Op.orrShl 0).eval [x,y] = Op.orr.eval [x,y] := by
  change x ||| (y <<< 0) = x ||| y
  simp

theorem csetm_ne (nf zf cf vf : BitVec 64) :
    (Op.cselc 0#4).eval [nf,zf,cf,vf,0#64,~~~(0#64)] =
      (Op.cselc 1#4).eval [0#64,zf,0#64,0#64,~~~(0#64),0#64] := by
  change (if zf != 0#64 then 0#64 else ~~~(0#64)) =
    (if !(zf != 0#64) then ~~~(0#64) else 0#64)
  cases h : (zf != 0#64) <;> rfl

def combined (x : LimbWords) : BitVec 64 := ((x.w0 ||| x.w1) ||| x.w2) ||| x.w3

theorem value_zero (x : LimbWords) : x.value = 0 ↔
    x.w0 = 0#64 ∧ x.w1 = 0#64 ∧ x.w2 = 0#64 ∧ x.w3 = 0#64 := by
  have word0 (w : BitVec 64) : w.toNat = 0 ↔ w = 0#64 := by
    constructor
    · intro h; exact BitVec.eq_of_toNat_eq h
    · intro h; rw [h]; rfl
  have packed : x.value = 0 ↔ x.w0.toNat = 0 ∧ x.w1.toNat = 0 ∧
      x.w2.toNat = 0 ∧ x.w3.toNat = 0 := by
    simp only [LimbWords.value,pack4,limbRadix]
    omega
  simpa only [word0] using packed

theorem combined_zero (x : LimbWords) : combined x = 0#64 ↔ x.value = 0 := by
  simp only [combined,BitVec.or_eq_zero_iff,value_zero,and_assoc]

theorem compare_zero (x : BitVec 64) : Op.sbc3Z.eval [x,0#64,1#64] = b01 (x == 0#64) := by
  change b01 (x+~~~(0#64)+1#64 == 0#64) = _
  have h : ~~~(0#64)+1#64 = 0#64 := by decide
  simp only [BitVec.add_assoc,h,BitVec.add_zero]

def maskWord (x : LimbWords) : BitVec 64 :=
  (Op.cselc 1#4).eval [0#64,Op.sbc3Z.eval [combined x,0#64,1#64],0#64,0#64,~~~(0#64),0#64]

theorem maskWord_correct (x : LimbWords) :
    maskWord x = if x.value = 0 then 0#64 else ~~~(0#64) := by
  unfold maskWord
  rw [compare_zero]
  change (if condHolds 1#4 0#64 (b01 (combined x == 0#64)) 0#64 0#64
    then ~~~(0#64) else 0#64) = _
  by_cases zero : combined x = 0#64
  · have val : x.value = 0 := (combined_zero x).mp zero
    simp [zero,val,b01,condHolds]
  · have val : x.value ≠ 0 := by intro h; exact zero ((combined_zero x).mpr h)
    simp [zero,val,b01,condHolds]

/-- The actual BIC value is mask AND NOT (976 OR 2^32). -/
def modulusWords (x : LimbWords) : LimbWords :=
  let mask := maskWord x
  ⟨Op.and.eval [mask,Op.not.eval [Op.orr.eval [976#64,4294967296#64]]],mask,mask,mask⟩

theorem modulusWords_value (x : LimbWords) :
    (modulusWords x).value = if x.value = 0 then 0 else modulus := by
  unfold modulusWords
  rw [maskWord_correct]
  by_cases zero : x.value = 0 <;> simp only [zero,↓reduceIte]
  · change (⟨0#64 &&& ~~~(976#64 ||| 4294967296#64),0#64,0#64,0#64⟩ : LimbWords).value = 0
    decide
  · change (⟨~~~(0#64) &&& ~~~(976#64 ||| 4294967296#64),~~~(0#64),~~~(0#64),~~~(0#64)⟩ : LimbWords).value = modulus
    decide

def coreNeg4 (x : LimbWords) : LimbWords := (SecpMath.coreChain4 (modulusWords x) x).1

theorem coreNeg4_eq_core (x : LimbWords) (hx : x.value < modulus) :
    (coreNeg4 x).value = subCore modulus 0 x.value := by
  have chain := (SecpMath.coreChain4_correct (modulusWords x) x).1
  change (coreNeg4 x).value = _ at chain
  rw [modulusWords_value] at chain
  rw [chain]
  by_cases zero : x.value = 0
  · simp [zero,subCore]
  · have low : modulus-x.value < radix := by have := radix_split; have := correction_pos; omega
    have balance : radix-x.value+modulus = (modulus-x.value)+radix := by
      have := radix_split; omega
    simp only [zero,↓reduceIte]
    rw [balance]
    simp only [Nat.add_mod_right,Nat.mod_eq_of_lt low]
    simp only [subCore]
    split <;> omega

theorem coreNeg4_correct (x : LimbWords) (hx : x.value < modulus) :
    (coreNeg4 x).value < modulus ∧ ((coreNeg4 x).value : Int) =
      (-(x.value : Int)) % (modulus : Int) := by
  rw [coreNeg4_eq_core x hx]
  have result := subCore_int modulus 0 x.value modulus_pos hx
  simpa using And.intro (subCore_lt modulus 0 x.value modulus_pos hx) result

#print axioms combined_zero
#print axioms maskWord_correct
#print axioms modulusWords_value
#print axioms coreNeg4_correct
end SecpMath.Negation
