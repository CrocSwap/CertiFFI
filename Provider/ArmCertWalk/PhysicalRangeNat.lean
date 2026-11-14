import ArmCertWalk.PhysicalRange
import ArmCertWalk.RangeMasks

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

theorem encodedBits_legal (ips : BitVec 3) : LegalPAMax (encodedBits ips) := by
  unfold encodedBits
  repeat' first | split | simp [LegalPAMax]

theorem formatCap_legal (lpa lpa2 : Bool) : LegalPAMax (formatCap lpa lpa2) := by
  cases lpa <;> cases lpa2 <;> simp [LegalPAMax, formatCap]

theorem legalPAMax_min (left right : Int) (a : LegalPAMax left) (b : LegalPAMax right) :
    LegalPAMax (min left right) := by
  simp only [Int.min_def]
  split <;> assumption

theorem effectiveBits_cases (config : PhysicalConfig) (legal : LegalPAMax config.paMax) :
    effectiveBits config = 32 ∨ effectiveBits config = 36 ∨ effectiveBits config = 40 ∨
    effectiveBits config = 42 ∨ effectiveBits config = 44 ∨ effectiveBits config = 48 ∨
    effectiveBits config = 52 := by
  have actual := legalPAMax_min _ _ (encodedBits_legal config.ips)
    (legalPAMax_min _ _ (formatCap_legal config.lpa config.lpa2) legal)
  have bounded := effectiveBits_bounds config legal
  change LegalPAMax (effectiveBits config) at actual
  unfold LegalPAMax at actual
  omega

theorem high_mask_zero (address : BitVec 56) (bits : Nat)
    (bound : address.toNat < 2^bits) : address &&& ((BitVec.allOnes (56 - bits)).setWidth 56 <<< bits) = 0#56 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases below : i < bits
  · simp [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes,
      below, show ¬bits ≤ i by omega, ← BitVec.getLsbD_eq_getElem]
  · have addressZero : address.getLsbD i = false := by
      change address.toNat.testBit i = false
      apply Nat.testBit_lt_two_pow
      exact Nat.lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) (by omega))
    simp [BitVec.getLsbD_and, addressZero, ← BitVec.getLsbD_eq_getElem]

theorem physical_range_in_bounds (config : PhysicalConfig) (address : BitVec 56)
    (legal : LegalPAMax config.paMax) (bound : address.toNat < 2 ^ (effectiveBits config).toNat) :
    is_zero_subrange address 55 (effectiveBits config) = true := by
  rw [RangeMasks.normalize address _ (effectiveBits_cases config legal)]
  rw [high_mask_zero address _ bound]
  decide

theorem oaOutOfRange_false (config : PhysicalConfig) (address : BitVec 56) (state : State)
    (current : PhysicalAt config state) (bound : address.toNat < 2 ^ (effectiveBits config).toNat) :
    AArch64_OAOutOfRange address 0#1 config.ips .TGx_4KB state =
      .ok false (physicalPost state) := by
  rw [oaOutOfRange_eq config address state current,
    physical_range_in_bounds config address current.legal bound]
  rfl

#print axioms effectiveBits_cases
#print axioms high_mask_zero
#print axioms physical_range_in_bounds
#print axioms oaOutOfRange_false

end ArmCertWalk
