-- Exact frozen Core addition operations; machine execution joins are separate.
import SecpMath.Add

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000

namespace SecpMath.Addition
open ArmCertValue

theorem add3_limb (x y : BitVec 64) (carry : Nat) (hc : carry ≤ 1) :
    (Op.add3.eval [x,y,BitVec.ofNat 64 carry]).toNat =
      limbSum x.toNat y.toNat carry := by
  have hn : (BitVec.ofNat 64 carry).toNat = carry := Nat.mod_eq_of_lt (by omega)
  change (x+y+BitVec.ofNat 64 carry).toNat = _
  simp only [BitVec.toNat_add, hn, limbSum, limbRadix, Nat.mod_add_mod]

theorem carry3_limb (x y : BitVec 64) (carry : Nat) (hc : carry ≤ 1) :
    (Op.carry3.eval [x,y,BitVec.ofNat 64 carry]).toNat =
      limbCarry x.toNat y.toNat carry := by
  have hn : (BitVec.ofNat 64 carry).toNat = carry := Nat.mod_eq_of_lt (by omega)
  rw [limb_carry_flag _ _ _ x.isLt y.isLt hc]
  change (b01 (decide (2^64 ≤ x.toNat+y.toNat+(BitVec.ofNat 64 carry).toNat))).toNat = _
  rw [hn]
  change (b01 (decide (2^64 ≤ x.toNat+y.toNat+carry))).toNat =
    if 2^64 ≤ x.toNat+y.toNat+carry then 1 else 0
  by_cases over : 2^64 ≤ x.toNat+y.toNat+carry <;> simp [b01, over]

theorem carry3_word (x y : BitVec 64) (carry : Nat) (hc : carry ≤ 1) :
    Op.carry3.eval [x,y,BitVec.ofNat 64 carry] =
      BitVec.ofNat 64 (limbCarry x.toNat y.toNat carry) := by
  apply BitVec.eq_of_toNat_eq
  rw [carry3_limb x y carry hc]
  exact (Nat.mod_eq_of_lt (by have := limb_carry_le_one _ _ _ x.isLt y.isLt hc; omega)).symm

def coreChain4 (x y : LimbWords) : LimbWords × BitVec 64 :=
  let d0 := Op.add3.eval [x.w0,y.w0,0#64]
  let c0 := Op.carry3.eval [x.w0,y.w0,0#64]
  let d1 := Op.add3.eval [x.w1,y.w1,c0]
  let c1 := Op.carry3.eval [x.w1,y.w1,c0]
  let d2 := Op.add3.eval [x.w2,y.w2,c1]
  let c2 := Op.carry3.eval [x.w2,y.w2,c1]
  let d3 := Op.add3.eval [x.w3,y.w3,c2]
  let c3 := Op.carry3.eval [x.w3,y.w3,c2]
  (⟨d0,d1,d2,d3⟩,c3)

theorem coreChain4_add4 (x y : LimbWords) :
    ((coreChain4 x y).1.value,(coreChain4 x y).2.toNat) =
      add4 x.w0.toNat x.w1.toNat x.w2.toNat x.w3.toNat
        y.w0.toNat y.w1.toNat y.w2.toNat y.w3.toNat := by
  let c0 := limbCarry x.w0.toNat y.w0.toNat 0
  let c1 := limbCarry x.w1.toNat y.w1.toNat c0
  let c2 := limbCarry x.w2.toNat y.w2.toNat c1
  have h0 : c0 ≤ 1 := limb_carry_le_one _ _ _ x.w0.isLt y.w0.isLt (by omega)
  have h1 : c1 ≤ 1 := limb_carry_le_one _ _ _ x.w1.isLt y.w1.isLt h0
  have h2 : c2 ≤ 1 := limb_carry_le_one _ _ _ x.w2.isLt y.w2.isLt h1
  have f0 := carry3_word x.w0 y.w0 0 (by omega)
  have f1 := carry3_word x.w1 y.w1 c0 h0
  have f2 := carry3_word x.w2 y.w2 c1 h1
  have f3 := carry3_limb x.w3 y.w3 c2 h2
  have d0 := add3_limb x.w0 y.w0 0 (by omega)
  have d1 := add3_limb x.w1 y.w1 c0 h0
  have d2 := add3_limb x.w2 y.w2 c1 h1
  have d3 := add3_limb x.w3 y.w3 c2 h2
  change Op.carry3.eval [x.w0,y.w0,0#64] = BitVec.ofNat 64 c0 at f0
  change Op.carry3.eval [x.w1,y.w1,BitVec.ofNat 64 c0] = BitVec.ofNat 64 c1 at f1
  change Op.carry3.eval [x.w2,y.w2,BitVec.ofNat 64 c1] = BitVec.ofNat 64 c2 at f2
  simp only [coreChain4, f0, f1, f2, LimbWords.value, d0, d1, d2, d3, f3]
  rfl

theorem coreChain4_balance (x y : LimbWords) :
    (coreChain4 x y).1.value + radix*(coreChain4 x y).2.toNat = x.value+y.value := by
  have h := coreChain4_add4 x y
  have low := congrArg Prod.fst h
  have carry := congrArg Prod.snd h
  simp only at low
  simp only at carry
  rw [low,carry]
  exact add4_balance ..

theorem coreChain4_low (x y : LimbWords) :
    (coreChain4 x y).1.value = (x.value+y.value)%radix := by
  have h := congrArg Prod.fst (coreChain4_add4 x y)
  exact h.trans (add4_low ..)

theorem carry3_le_one (x y carry : BitVec 64) :
    (Op.carry3.eval [x,y,carry]).toNat ≤ 1 := by
  change (b01 _).toNat ≤ 1
  unfold b01
  split <;> decide

theorem coreChain4_flag (x y : LimbWords) : (coreChain4 x y).2.toNat ≤ 1 :=
  carry3_le_one ..

def coreComparison (d : LimbWords) : BitVec 64 :=
  Op.carry3.eval [Op.and.eval [Op.and.eval [d.w1,d.w2],d.w3],0#64,
    Op.carry3.eval [d.w0,BitVec.ofNat 64 correction,0#64]]

theorem coreComparison_pure (d : LimbWords) :
    (coreComparison d).toNat = comparisonCarry d.w0.toNat d.w1.toNat d.w2.toNat d.w3.toNat := by
  have k : (BitVec.ofNat 64 correction).toNat = correction := Nat.mod_eq_of_lt (by decide)
  have low := carry3_word d.w0 (BitVec.ofNat 64 correction) 0 (by omega)
  simp only [k] at low
  change Op.carry3.eval [d.w0,BitVec.ofNat 64 correction,0#64] = _ at low
  have lowBound := limb_carry_le_one d.w0.toNat correction 0 d.w0.isLt (by decide) (by omega)
  unfold coreComparison
  rw [low, carry3_limb _ _ _ lowBound]
  change limbCarry ((d.w1 &&& d.w2) &&& d.w3).toNat 0 _ = _
  simp only [BitVec.toNat_and, comparisonCarry]

theorem coreComparison_correct (d : LimbWords) :
    (coreComparison d).toNat = if modulus ≤ d.value then 1 else 0 := by
  rw [coreComparison_pure]
  exact comparisonCarry_correct _ _ _ _ d.w0.isLt d.w1.isLt d.w2.isLt d.w3.isLt

/-- NE observes Z of the small sum of the original and comparison carries. -/
theorem select_from_carries (n cf v : BitVec 64) (carry test : Nat)
    (hc : carry ≤ 1) (ht : test ≤ 1) :
    (Op.cselc 1#4).eval [n,
      Op.add3Z.eval [BitVec.ofNat 64 carry,0#64,BitVec.ofNat 64 test],cf,v,
      BitVec.ofNat 64 correction,0#64] =
      BitVec.ofNat 64 (if carry+test = 0 then 0 else correction) := by
  change (if condHolds 1#4 n
    (b01 (BitVec.ofNat 64 carry+0#64+BitVec.ofNat 64 test == 0#64)) cf v
    then BitVec.ofNat 64 correction else 0#64) = _
  have c : carry = 0 ∨ carry = 1 := by omega
  have t : test = 0 ∨ test = 1 := by omega
  rcases c with rfl | rfl <;> rcases t with rfl | rfl <;> simp [condHolds,b01]

theorem adc_zero (carry : BitVec 64) : Op.add3.eval [0#64,0#64,carry] = carry := by
  change 0#64+0#64+carry = carry
  simp

def selectCorrectionWords (carry test : BitVec 64) : BitVec 64 :=
  (Op.cselc 1#4).eval [0#64,
    Op.add3Z.eval [Op.add3.eval [0#64,0#64,carry],0#64,test],0#64,0#64,
    BitVec.ofNat 64 correction,0#64]

theorem selectCorrectionWords_pure (carry test : BitVec 64)
    (hc : carry.toNat ≤ 1) (ht : test.toNat ≤ 1) :
    selectCorrectionWords carry test =
      BitVec.ofNat 64 (if carry.toNat+test.toNat = 0 then 0 else correction) := by
  have original : carry = BitVec.ofNat 64 carry.toNat := by simp
  have other : test = BitVec.ofNat 64 test.toNat := by simp
  have sel := select_from_carries 0#64 0#64 0#64 _ _ hc ht
  unfold selectCorrectionWords
  rw [adc_zero]
  simpa only [← original,← other] using sel

def selectedCorrection (x y : LimbWords) : BitVec 64 :=
  selectCorrectionWords (coreChain4 x y).2 (coreComparison (coreChain4 x y).1)

theorem selectedCorrection_correct (x y : LimbWords) :
    selectedCorrection x y = BitVec.ofNat 64 (if modulus ≤ x.value+y.value then correction else 0) := by
  have flag := coreChain4_flag x y
  have cmp := coreComparison_correct (coreChain4 x y).1
  have cmpBound : (coreComparison (coreChain4 x y).1).toNat ≤ 1 := carry3_le_one ..
  have balance := coreChain4_balance x y
  have low := (coreChain4 x y).1.value_lt
  have k : modulus < radix := by decide
  rw [selectedCorrection, selectCorrectionWords_pure _ _ flag cmpBound]
  have zero : (coreChain4 x y).2.toNat + (coreComparison (coreChain4 x y).1).toNat = 0 ↔
      ¬ modulus ≤ x.value+y.value := by
    by_cases ge : modulus ≤ (coreChain4 x y).1.value
    · simp only [ge, ↓reduceIte] at cmp
      rw [cmp]
      omega
    · simp only [ge, ↓reduceIte] at cmp
      rw [cmp]
      simp only [radix] at balance k low
      omega
  by_cases ge : modulus ≤ x.value+y.value <;>
    simp only [zero,ge,not_true_eq_false,not_false_eq_true,↓reduceIte]

def coreAdd4 (x y : LimbWords) : LimbWords :=
  (coreChain4 (coreChain4 x y).1 ⟨selectedCorrection x y,0#64,0#64,0#64⟩).1

theorem coreAdd4_eq_wrapped (x y : LimbWords) :
    (coreAdd4 x y).value = wrappedAdd x.value y.value := by
  have wordValue : (⟨selectedCorrection x y,0#64,0#64,0#64⟩ : LimbWords).value =
      if modulus ≤ x.value+y.value then correction else 0 := by
    rw [selectedCorrection_correct]
    by_cases ge : modulus ≤ x.value+y.value <;>
      simp only [ge,↓reduceIte] <;>
      simp [LimbWords.value,pack4,Nat.mod_eq_of_lt (show correction < 2^64 by decide)]
  unfold coreAdd4
  rw [coreChain4_low,wordValue,coreChain4_low]
  rfl

theorem coreAdd4_correct (x y : LimbWords) (hx : x.value < modulus) (hy : y.value < modulus) :
    (coreAdd4 x y).value < modulus ∧ (coreAdd4 x y).value = (x.value+y.value)%modulus := by
  rw [coreAdd4_eq_wrapped]
  exact wrappedAdd_correct x.value y.value hx hy

#print axioms add3_limb
#print axioms carry3_limb
#print axioms coreChain4_add4
#print axioms coreChain4_balance
#print axioms coreChain4_low
#print axioms coreComparison_correct
#print axioms selectedCorrection_correct
#print axioms coreAdd4_correct
end SecpMath.Addition
