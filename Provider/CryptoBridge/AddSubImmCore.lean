import Bridge.Step
import Bridge.Proj
import Bridge.Awc
import Bridge.Opnd
import CryptoBridge.RW
import BridgeV2.StateProjectionM
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to CryptoBridge.AddSubImmCoreLNSym.
namespace CryptoBridge.AddSubImmCore

/-! Shared lemmas for the ADD/SUB (immediate) bridge family (armcert-crypto). -/

theorem b01 : ((0#1 : BitVec 1) == 1#1) = false := rfl

theorem b11 : ((1#1 : BitVec 1) == 1#1) = true := rfl

theorem wb64 : Sail.Int.toNatChecked (if ((1#1 : BitVec 1) == 1#1) = true then (64 : Int) else 32) = 64 := rfl

theorem wb32 : Sail.Int.toNatChecked (if ((0#1 : BitVec 1) == 1#1) = true then (64 : Int) else 32) = 32 := rfl

theorem ib64 : (if ((1#1 : BitVec 1) == 1#1) = true then (64 : Int) else 32) = 64 := rfl

theorem ib32 : (if ((0#1 : BitVec 1) == 1#1) = true then (64 : Int) else 32) = 32 := rfl

theorem t64 : (if true = true then (64 : Int) else 32) = 64 := rfl

theorem t32 : (if false = true then (64 : Int) else 32) = 32 := rfl

theorem tn64 : Sail.Int.toNatChecked (if true = true then (64 : Int) else 32) = 64 := rfl

theorem tn32 : Sail.Int.toNatChecked (if false = true then (64 : Int) else 32) = 32 := rfl

theorem l64 : (if (1#1 : BitVec 1) = 1#1 then (64 : Nat) else 32) = 64 := rfl

theorem l32 : (if (0#1 : BitVec 1) = 1#1 then (64 : Nat) else 32) = 32 := rfl

theorem m0 {α : Type} (a b : α) : (match (0#1 : BitVec 1) with | 0#1 => a | _ => b) = a := rfl

theorem m1 {α : Type} (a b : α) : (match (1#1 : BitVec 1) with | 0#1 => a | _ => b) = b := rfl

theorem app0 (x : BitVec 12) (i : Nat) : (BitVec.append (0#52 : BitVec 52) x).getLsbD i = x.getLsbD i := by
  rw [BitVec.append_eq, BitVec.getLsbD_append]
  by_cases h : i < 12
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge x i (by omega)]

theorem neg_imm_64_0 (imm12 : BitVec 12) :
    BitVec.zeroExtend 64 (~~~(0#52 +++ imm12)) = ~~~(Sail.BitVec.zeroExtend imm12 64) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [Sail.BitVec.zeroExtend, BitVec.getLsbD_append, hi]
  rw [← BitVec.getLsbD_eq_getElem]
  exact app0 imm12 i

theorem neg_imm_32_0 (imm12 : BitVec 12) :
    BitVec.zeroExtend 32 (~~~(0#52 +++ imm12)) = ~~~(Sail.BitVec.zeroExtend imm12 32) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [Sail.BitVec.zeroExtend, BitVec.getLsbD_append, hi]
  first
    | (rw [← BitVec.getLsbD_eq_getElem]; exact app0 imm12 i)
    | exact app0 imm12 i

theorem ga (x : BitVec 12) (i : Nat) :
    (@HAppend.hAppend (BitVec 52) (BitVec 12) (BitVec 64) (@BitVec.instHAppendHAddNat 52 12) 0#52 x).getLsbD i
      = x.getLsbD i := app0 x i

theorem gb (x : BitVec 12) (i : Nat) :
    (@HAppend.hAppend (BitVec 12) (BitVec 12) (BitVec 24) (@BitVec.instHAppendHAddNat 12 12) x 0#12).getLsbD i
      = (decide (12 ≤ i) && x.getLsbD (i - 12)) := by
  show (BitVec.append x 0#12).getLsbD i = _
  rw [BitVec.append_eq, BitVec.getLsbD_append]
  by_cases h : i < 12
  · simp [h]; intro h'; omega
  · simp [h]; omega

theorem neg_imm_64_1 (imm12 : BitVec 12) :
    BitVec.zeroExtend 64 (~~~((0#52 +++ imm12) <<< 12)) = ~~~(Sail.BitVec.zeroExtend (imm12 +++ 0#12) 64) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [Sail.BitVec.zeroExtend, BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, hi]
  simp only [← BitVec.getLsbD_eq_getElem, ga, gb]
  by_cases h : i < 12 <;> simp [h]

theorem neg_imm_32_1 (imm12 : BitVec 12) :
    BitVec.zeroExtend 32 (~~~((0#52 +++ imm12) <<< 12)) = ~~~(Sail.BitVec.zeroExtend (imm12 +++ 0#12) 32) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [Sail.BitVec.zeroExtend, BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, hi]
  simp only [ga, gb]
  by_cases h : i < 12 <;> simp [h]

theorem pos_imm_64_0 (imm12 : BitVec 12) :
    BitVec.zeroExtend 64 (0#52 +++ imm12) = Sail.BitVec.zeroExtend imm12 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [Sail.BitVec.zeroExtend, BitVec.getLsbD_append, hi]
  first
    | (rw [← BitVec.getLsbD_eq_getElem]; exact app0 imm12 i)
    | exact app0 imm12 i
    | (simp only [← BitVec.getLsbD_eq_getElem, ga]; done)
    | simp only [ga]

theorem pos_imm_32_0 (imm12 : BitVec 12) :
    BitVec.zeroExtend 32 (0#52 +++ imm12) = Sail.BitVec.zeroExtend imm12 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [Sail.BitVec.zeroExtend, BitVec.getLsbD_append, hi]
  first
    | (rw [← BitVec.getLsbD_eq_getElem]; exact app0 imm12 i)
    | exact app0 imm12 i
    | (simp only [← BitVec.getLsbD_eq_getElem, ga]; done)
    | simp only [ga]

theorem pos_imm_64_1 (imm12 : BitVec 12) :
    BitVec.zeroExtend 64 ((0#52 +++ imm12) <<< 12) = Sail.BitVec.zeroExtend (imm12 +++ 0#12) 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [Sail.BitVec.zeroExtend, BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, hi]
  simp only [← BitVec.getLsbD_eq_getElem, ga, gb]
  by_cases h : i < 12 <;> simp [h] <;> intro _ <;> omega

theorem pos_imm_32_1 (imm12 : BitVec 12) :
    BitVec.zeroExtend 32 ((0#52 +++ imm12) <<< 12) = Sail.BitVec.zeroExtend (imm12 +++ 0#12) 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [Sail.BitVec.zeroExtend, BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, hi]
  simp only [ga, gb]
  by_cases h : i < 12 <;> simp [h] <;> intro _ <;> omega

end CryptoBridge.AddSubImmCore

