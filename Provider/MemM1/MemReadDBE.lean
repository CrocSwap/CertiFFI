import MemM1.MemReadIF
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.MemReadDBE
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality

drive_spec be_native, be_eq : fun (s : State)
    (hEL : s.regs.PSTATE.EL = 0#2) (hnRW : s.regs.PSTATE.nRW = 0#1)
    (hR : s.regs.FeatureImpl[232] = false) (hVHE : s.regs.FeatureImpl[54] = true)
    (hAA : s.regs.FeatureImpl[4] = true)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1)
    (hE2H : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 34 34 = 1#1)
    (hTGE : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 27 27 = 1#1) =>
  BigEndian .AccessType_GPR s

/-- `BigEndian GPR` at EL0 in the EL2&0 host regime reads SCTLR_EL2.E0E (bit 24): little-endian
    when it is 0. -/
theorem be_false (s : State)
    (hEL : s.regs.PSTATE.EL = 0#2) (hnRW : s.regs.PSTATE.nRW = 0#1)
    (hR : s.regs.FeatureImpl[232] = false) (hVHE : s.regs.FeatureImpl[54] = true)
    (hAA : s.regs.FeatureImpl[4] = true)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1)
    (hE2H : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 34 34 = 1#1)
    (hTGE : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 27 27 = 1#1)
    (hE0E : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCTLR_EL2) 24 24 = 0#1) :
    ∃ t, BigEndian .AccessType_GPR s = .ok false t ∧ Frame s t := by
  rw [be_eq s hEL hnRW hR hVHE hAA hNS hE2H hTGE]
  observe_simp [Frame, be_native]
  refine ⟨_, ⟨?_, rfl⟩, rfl, rfl, rfl⟩
  simp only [Mk_SCTLRType, Mk_SCRType, hNS, not_true_eq_false, false_and, ↓reduceIte]
  exact hE0E

#print axioms be_false

end MemM1.MemReadDBE
