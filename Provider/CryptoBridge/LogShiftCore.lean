import CryptoBridge.AddSubShiftCore
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace CryptoBridge.LogShiftCore

/-- LNSym's 32-bit legality test for logical (shifted register), under the premise. -/
theorem hand32' (imm6 : BitVec 6) (h : imm6.toNat < 32) : imm6 &&& 32#6 = 0#6 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h5 : imm6.getLsbD 5 = false := by
    simp only [BitVec.getLsbD]; exact Nat.testBit_lt_two_pow (by simpa using h)
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;>
    subst h <;> simp [h5, ← BitVec.getLsbD_eq_getElem]

theorem hand32 (imm6 : BitVec 6) (h : imm6.toNat < 32) : (imm6 &&& 32 ≠ 0) = False := by
  have := hand32' imm6 h
  simp only [ne_eq, eq_iff_iff, iff_false, Classical.not_not]
  exact this

/-- Native ROR (rotate by a Nat amount) is LNSym's rotateRight. -/
theorem ror_eq {w : Nat} (x : BitVec w) (n : Nat) : ArmFull.Functions.ROR x n = x.rotateRight n := by
  unfold ArmFull.Functions.ROR
  split
  · rename_i h
    have : n = 0 := by simpa using h
    subst this
    simp only [Sail.BitVec.castWidth_eq, BitVec.rotateRight, Nat.zero_mod, BitVec.rotateRightAux,
      BitVec.ushiftRight_zero, Nat.sub_zero, BitVec.shiftLeft_eq_zero (Nat.le_refl w), BitVec.or_zero]
  · rename_i h
    rw [BitVec.rotateRight_def]
    simp only [Sail.BitVec.castWidth_eq, Sail.BitVec.length]
    rcases Nat.eq_zero_or_pos w with hw | hw
    · subst hw; exact Subsingleton.elim _ _
    · have hm : n % w < w := Nat.mod_lt _ hw
      have e : ((w : Int) - ((n.mod w : Nat) : Int)) = ((w - n % w : Nat) : Int) := by
        rw [show n.mod w = n % w from rfl]; omega
      rw [e, show n.mod w = n % w from rfl]
      rfl

#print axioms hand32
end CryptoBridge.LogShiftCore
