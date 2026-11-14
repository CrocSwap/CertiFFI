import MemM1.S1Callees
import MemM1.Debug
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
namespace MemM1.Bits
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality

/-- S1Enabled (EL2&0) from the SCTLR_EL2.M bit only (eval ProfileEL20.e3 form). -/
theorem en (acctype : AccessType) (s : State)
    (hM : _get_SCTLR_EL2_Type_M (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1) :
    ∀ t, Frame s t → ∃ u, AArch64_S1Enabled .Regime_EL20 acctype t = .ok true u ∧ Frame t u := by
  intro t ht
  have hM' : _get_SCTLR_EL2_Type_M (t.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1 := by rw [ht.1]; exact hM
  rw [MemM1.S1Callees.en_eq]
  observe_simp [Frame, MemM1.S1Callees.en_native]
  exact ⟨t, ⟨hM', rfl⟩, rfl, rfl, rfl⟩

theorem mde (R : Regs) (h : _get_MDSCR_EL1_Type_MDE (R.bank_BitVec_64 .MDSCR_EL1) = 0#1) :
    Sail.BitVec.extractLsb (R.bank_BitVec_64 Bank_BitVec_64.MDSCR_EL1) 15 15 = 0#1 := h
theorem hde (R : Regs) (h : _get_EDSCR_Type_HDE (R.bank_BitVec_32 ._EDSCR) = 0#1) :
    Sail.BitVec.extractLsb (R.bank_BitVec_32 Bank_BitVec_32._EDSCR) 14 14 = 0#1 := h
theorem spe (R : Regs) (h : R.bank_Bool .SPESampleInFlight = false) :
    Register.SPESampleInFlight.get R = false := h

#print axioms en
end MemM1.Bits
