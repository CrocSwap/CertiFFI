-- BR8 split B2 (post-seal branch): caller-side forms of BranchTo's two composition pins.
import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
set_option autoImplicit false
namespace BR8Pins
theorem bit55_of_lt (x : BitVec 64) (h : x.toNat < 2 ^ 55) : BitVec.access x 55 = 0#1 := by
  have hb : x.getLsbD 55 = false := by
    simp only [BitVec.getLsbD]
    exact Nat.testBit_lt_two_pow h
  have h2 : x[55]! = false := by
    rw [getElem!_pos x 55 (by decide), ← BitVec.getLsbD_eq_getElem]; exact hb
  simp only [BitVec.access, h2]; rfl
theorem vhe_bang (s : SequentialState Regs oracleChoiceSource) (h : s.regs.FeatureImpl[54] = true) :
    s.regs.FeatureImpl[54]! = true := by
  simpa using h
end BR8Pins
