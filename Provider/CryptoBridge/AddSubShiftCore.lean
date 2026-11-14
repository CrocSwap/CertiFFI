import CryptoBridge.AddSubImmCore
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to CryptoBridge.AddSubShiftCoreLNSym.
namespace CryptoBridge.AddSubShiftCore


/-! Shift-operand lemmas for the shifted-register ALU bridges (armcert-crypto). The roots shift by
`(n : Int)` through Sail's `HShiftLeft (BitVec w) Int` instance, instantiated at the unreduced
datasize; LNSym shifts by `n : Nat`. Stated at the roots' exact instance form (rfl/dsimp). -/

theorem shl64 (x : BitVec 64) (n : Nat) :
    @HShiftLeft.hShiftLeft (BitVec 64) Int (BitVec 64)
      (@Sail.instHShiftLeftBitVecInt_sail (Sail.Int.toNatChecked (if (1#1 : BitVec 1) = 1#1 then (64 : Int) else 32)))
      x (n : Int) = x <<< n := rfl

theorem shl32 (x : BitVec 32) (n : Nat) :
    @HShiftLeft.hShiftLeft (BitVec 32) Int (BitVec 32)
      (@Sail.instHShiftLeftBitVecInt_sail (Sail.Int.toNatChecked (if (0#1 : BitVec 1) = 1#1 then (64 : Int) else 32)))
      x (n : Int) = x <<< n := rfl

theorem shr_nat {w : Nat} (x : BitVec w) (n : Nat) :
    @HShiftLeft.hShiftLeft (BitVec w) Int (BitVec w) (@Sail.instHShiftLeftBitVecInt_sail w) x (-(n : Int)) = x >>> n := by
  rcases n with _ | n
  · show BitVec.shiftLeft x 0 = x >>> 0
    simp
  · rfl

theorem shr64 (x : BitVec 64) (n : Nat) :
    @HShiftRight.hShiftRight (BitVec 64) Int (BitVec 64)
      (@Sail.instHShiftRightBitVecInt_sail (Sail.Int.toNatChecked (if (1#1 : BitVec 1) = 1#1 then (64 : Int) else 32)))
      x (n : Int) = x >>> n := shr_nat x n

theorem shr32 (x : BitVec 32) (n : Nat) :
    @HShiftRight.hShiftRight (BitVec 32) Int (BitVec 32)
      (@Sail.instHShiftRightBitVecInt_sail (Sail.Int.toNatChecked (if (0#1 : BitVec 1) = 1#1 then (64 : Int) else 32)))
      x (n : Int) = x >>> n := shr_nat x n

theorem one1 : (1 : BitVec 1) = 1#1 := rfl

theorem zero1 : (0 : BitVec 1) = 0#1 := rfl

/-- The root's 32-bit legality test (imm6<5> = 1 is UNDEFINED) under the premise. -/
theorem nj (imm6 : BitVec 6) (h : imm6.toNat < 32) : ¬ BitVec.join1 [BitVec.access imm6 5] = 1#1 := by
  have hb : imm6.getLsbD 5 = false := by
    simp only [BitVec.getLsbD]; exact Nat.testBit_lt_two_pow (by simpa using h)
  intro e
  have e2 := congrArg (fun v : BitVec 1 => v.getLsbD 0) e
  simp [Sail.BitVec.join1, Sail.BitVec.access, BitVec.ofBoolListBE, hb] at e2
  have h5 : imm6[5]! = false := by
    first
      | (rw [getElem!_pos imm6 5 (by decide)]; rw [← BitVec.getLsbD_eq_getElem]; exact hb)
      | (simp [BitVec.getElem!_eq_getLsbD]; exact hb)
      | simpa [BitVec.getLsbD_eq_getElem] using hb
  rw [h5] at e2
  revert e2; decide

end CryptoBridge.AddSubShiftCore

