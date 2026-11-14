import Pilot.S1Decode
import Pilot.ObservationSimp
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 300000
set_option maxRecDepth 1000000
namespace S1DecodeFacts
abbrev State := SequentialState Regs oracleChoiceSource
def bit (d : BitVec 64) (i : Nat) : BitVec 1 :=
  BitVec.setWidth 1 (Sail.BitVec.join1 [Sail.BitVec.access d i])

theorem bit_cases (x : BitVec 1) : x = 0#1 ∨ x = 1#1 := by
  have hx := x.isLt
  have h : x.toNat = 0 ∨ x.toNat = 1 := by omega
  rcases h with h | h
  · left; exact BitVec.eq_of_toNat_eq h
  · right; exact BitVec.eq_of_toNat_eq h

def classify (d : BitVec 64) (level : Int) : DescriptorType :=
  if bit d 0 = 0#1 then .DescriptorType_Invalid
  else if bit d 1 = 1#1 then
    if level = 3 then .DescriptorType_Leaf else .DescriptorType_Table
  else if level = 1 ∨ level = 2 then .DescriptorType_Leaf
  else .DescriptorType_Invalid

theorem native_eq (d : BitVec 64) (level : Int) (s : State) :
    S1Decode.native d level s = .ok (classify d level) s := by
  rcases bit_cases (bit d 0) with h0 | h0 <;>
    rcases bit_cases (bit d 1) with h1 | h1
  all_goals
    unfold bit at h0 h1
    simp at h0 h1
    observe_simp [S1Decode.native, classify, bit, FINAL_LEVEL]

theorem model_eq (d : BitVec 64) (level : Int) (s : State) :
    AArch64_DecodeDescriptorType d 0#1 0#1 .TGx_4KB level s =
      .ok (classify d level) s := by
  rw [S1Decode.complete, native_eq]

theorem table_before_final (d : BitVec 64) (level : Int) (h : level ≤ 3)
    (ht : classify d level = .DescriptorType_Table) : level < 3 := by
  by_cases hl : level = 3
  · subst level
    by_cases h0 : bit d 0 = 0#1 <;> by_cases h1 : bit d 1 = 1#1 <;>
      simp [classify, h0, h1] at ht
  · omega

#print axioms native_eq
#print axioms model_eq
#print axioms table_before_final
end S1DecodeFacts
