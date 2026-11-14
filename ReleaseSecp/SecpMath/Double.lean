-- Fixed LSL/LSR/EXTR word arithmetic for doubling; compiler/Sail joins separate.
import SecpMath.CoreAdd
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
namespace SecpMath.Doubling
open ArmCertValue SecpMath.Addition

private theorem shifted_low (a : Nat) : (a <<< 1)%limbRadix = (a%2^63) <<< 1 := by
  simp only [Nat.shiftLeft_eq,limbRadix]
  omega

def splice (higher lower : BitVec 64) : BitVec 64 := (higher <<< 1) ||| (lower >>> 63)

theorem top_lt_two (x : BitVec 64) : (x >>> 63).toNat < 2 := by
  have bound := x.isLt
  simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  omega

#check "CURRENT_DECL splice_toNat"

theorem splice_toNat (higher lower : BitVec 64) :
    (splice higher lower).toNat = (2*higher.toNat)%limbRadix+(lower >>> 63).toNat := by
  have low := top_lt_two lower
  have combine := Nat.shiftLeft_add_eq_or_of_lt (i:=1) low (higher.toNat%2^63)
  simp only [splice,BitVec.toNat_or,BitVec.toNat_shiftLeft]
  change ((higher.toNat <<< 1)%limbRadix) ||| (lower >>> 63).toNat = _
  rw [shifted_low higher.toNat,← combine,← shifted_low higher.toNat]
  simp only [Nat.shiftLeft_eq,Nat.mul_comm]

theorem splice_balance (higher lower : BitVec 64) :
    (splice higher lower).toNat + limbRadix*(higher >>> 63).toNat =
      higher.toNat+higher.toNat+(lower >>> 63).toNat := by
  rw [splice_toNat]
  have bound := higher.isLt
  have balance := Nat.mod_add_div (2*higher.toNat) limbRadix
  simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,limbRadix] at *
  omega

def doubledWords (x : LimbWords) : LimbWords :=
  ⟨x.w0 <<< 1,splice x.w1 x.w0,splice x.w2 x.w1,splice x.w3 x.w2⟩

#check "CURRENT_DECL doubledWords_balance"

theorem doubledWords_balance (x : LimbWords) :
    (doubledWords x).value + radix*(x.w3 >>> 63).toNat = x.value+x.value := by
  have h0 := splice_balance x.w0 (0#64)
  have h1 := splice_balance x.w1 x.w0
  have h2 := splice_balance x.w2 x.w1
  have h3 := splice_balance x.w3 x.w2
  have first : splice x.w0 (0#64) = x.w0 <<< 1 := by simp [splice]
  rw [first] at h0
  change (x.w0 <<< 1).toNat + limbRadix*(x.w0 >>> 63).toNat = x.w0.toNat+x.w0.toNat+0 at h0
  simp only [Nat.add_zero] at h0
  exact packed_balance _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3

theorem doubledWords_low (x : LimbWords) :
    (doubledWords x).value = (x.value+x.value)%radix := by
  have balance := congrArg (· % radix) (doubledWords_balance x)
  have low := (doubledWords x).value_lt
  simpa only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt low] using balance

#check "CURRENT_DECL selected_from_balance"

/-- Select the correction using only a derived packed-value/carry balance. -/

theorem selected_from_balance (words : LimbWords) (carry : BitVec 64) (total : Nat)
    (flag : carry.toNat ≤ 1) (balance : words.value+radix*carry.toNat = total) :
    selectCorrectionWords carry (coreComparison words) =
      BitVec.ofNat 64 (if modulus ≤ total then correction else 0) := by
  have cmp := coreComparison_correct words
  have cmpBound : (coreComparison words).toNat ≤ 1 := carry3_le_one ..
  have low := words.value_lt
  have k : modulus < radix := by decide
  rw [selectCorrectionWords_pure _ _ flag cmpBound]
  have zero : carry.toNat+(coreComparison words).toNat = 0 ↔ ¬ modulus ≤ total := by
    by_cases ge : modulus ≤ words.value
    · simp only [ge,↓reduceIte] at cmp
      rw [cmp]
      omega
    · simp only [ge,↓reduceIte] at cmp
      rw [cmp]
      simp only [radix] at balance k low
      omega
  by_cases ge : modulus ≤ total <;>
    simp only [zero,ge,not_true_eq_false,not_false_eq_true,↓reduceIte]

def correctionWord (x : LimbWords) : BitVec 64 :=
  selectCorrectionWords (x.w3 >>> 63) (coreComparison (doubledWords x))

theorem correctionWord_correct (x : LimbWords) :
    correctionWord x = BitVec.ofNat 64
      (if modulus ≤ x.value+x.value then correction else 0) := by
  exact selected_from_balance _ _ _ (by have := top_lt_two x.w3; omega)
    (doubledWords_balance x)

def coreDouble4 (x : LimbWords) : LimbWords :=
  (Addition.coreChain4 (doubledWords x) ⟨correctionWord x,0#64,0#64,0#64⟩).1

theorem coreDouble4_eq (x : LimbWords) :
    (coreDouble4 x).value = wrappedAdd x.value x.value := by
  have wordValue : (⟨correctionWord x,0#64,0#64,0#64⟩ : LimbWords).value =
      if modulus ≤ x.value+x.value then correction else 0 := by
    rw [correctionWord_correct]
    by_cases ge : modulus ≤ x.value+x.value <;>
      simp only [ge,↓reduceIte] <;>
      simp [LimbWords.value,pack4,Nat.mod_eq_of_lt (show correction < 2^64 by decide)]
  unfold coreDouble4
  rw [Addition.coreChain4_low,wordValue,doubledWords_low]
  rfl

#check "CURRENT_DECL coreDouble4_correct"

theorem coreDouble4_correct (x : LimbWords) (hx : x.value < modulus) :
    (coreDouble4 x).value < modulus ∧ (coreDouble4 x).value = (2*x.value)%modulus := by
  rw [coreDouble4_eq]
  simpa only [Nat.two_mul] using wrappedAdd_correct x.value x.value hx hx

#print axioms splice_toNat
#print axioms doubledWords_balance
#print axioms doubledWords_low
#print axioms coreDouble4_correct
end SecpMath.Doubling
