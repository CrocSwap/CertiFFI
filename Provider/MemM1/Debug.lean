import MemM1.Callees
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
namespace MemM1.Debug
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality

/-! `AArch64_CheckDebug` with self-hosted (MDSCR_EL1.MDE = 0) and halting (EDSCR.HDE = 0)
debug off: `generate_exception` is `GenerateDebugExceptions… && MDE == 1` (false on both the
NV2 and non-NV2 paths) and `HaltOnBreakpointOrWatchpoint` is `HaltingAllowed && HDE == 1 && …`
(false), so neither CheckWatchpoint nor CheckBreakpoint runs and the NoFault record is returned.
PSTATE.EL / FEAT_RME / FEAT_AA64EL0 / SCR_EL3.NS only let the symbolic driver resolve
`CurrentSecurityState` (the SecurityStateAtEL match); the result does not depend on it. -/

drive_spec cd_native, cd_eq : fun (va : BitVec 64) (acc : AccessDescriptor) (size : Int) (s : State)
    (hEL : s.regs.PSTATE.EL = 0#2)
    (hR : s.regs.FeatureImpl[232] = false) (hAA : s.regs.FeatureImpl[4] = true)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1)
    (hMDE : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.MDSCR_EL1) 15 15 = 0#1)
    (hHDE : Sail.BitVec.extractLsb (s.regs.bank_BitVec_32 Bank_BitVec_32._EDSCR) 14 14 = 0#1) =>
  AArch64_CheckDebug va acc size s

/-- CheckDebug returns a Fault_None record and only changes choice state, for any access
(data or instruction fetch), when PSTATE.EL = 0, FEAT_RME (bit 232) off, FEAT_AA64EL0 (bit 4) on,
SCR_EL3.NS (bit 0) = 1, MDSCR_EL1.MDE (bit 15) = 0 and EDSCR.HDE (bit 14) = 0. -/
theorem no_fault (va : BitVec 64) (acc : AccessDescriptor) (size : Int) (s : State)
    (hEL : s.regs.PSTATE.EL = 0#2)
    (hR : s.regs.FeatureImpl[232] = false) (hAA : s.regs.FeatureImpl[4] = true)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1)
    (hMDE : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.MDSCR_EL1) 15 15 = 0#1)
    (hHDE : Sail.BitVec.extractLsb (s.regs.bank_BitVec_32 Bank_BitVec_32._EDSCR) 14 14 = 0#1) :
    ∃ df t, AArch64_CheckDebug va acc size s = .ok df t ∧ df.statuscode = .Fault_None ∧ Frame s t := by
  rw [cd_eq va acc size s hEL hR hAA hNS hMDE hHDE]
  refine ⟨_, _, rfl, rfl, ?_, ?_, ?_⟩
  · simp only [apply_dite (fun t : State => t.regs), apply_ite (fun t : State => t.regs), dite_eq_ite, ite_self]
  · simp only [apply_dite (fun t : State => t.mem), apply_ite (fun t : State => t.mem), dite_eq_ite, ite_self]
  · simp only [apply_dite (fun t : State => t.events), apply_ite (fun t : State => t.events), dite_eq_ite, ite_self]

#print axioms no_fault
end MemM1.Debug
