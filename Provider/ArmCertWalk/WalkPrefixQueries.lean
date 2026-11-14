import ArmCertWalk.Profile
import GetEntry.Draws
import GetEntry.WP

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

def currentWalkEPD (regs : Regs) (va : BitVec 64) : BitVec 1 :=
  if AArch64_GetVARange va == .VARange_LOWER then
    _get_TCR_EL2_Type_EPD0 (regs.bank_BitVec_64 .TCR_EL2)
  else _get_TCR_EL2_Type_EPD1 (regs.bank_BitVec_64 .TCR_EL2)

theorem epd_el20_eq (va : BitVec 64) (state : State) :
    AArch64_S1EPD .Regime_EL20 va state = .ok (currentWalkEPD state.regs va) state := by
  have unpriv : HasUnprivileged .Regime_EL20 = true := rfl
  by_cases lower : AArch64_GetVARange va == .VARange_LOWER <;>
    simp only [AArch64_S1EPD, currentWalkEPD, unpriv, lower] <;> rfl

#print axioms epd_el20_eq
end ArmCertWalk
