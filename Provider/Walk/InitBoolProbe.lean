import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace InitBoolProbe
abbrev State := SequentialState Regs oracleChoiceSource
def tlb {α : Type} : EStateM.Result (Sail.Error exception) State α → Option Bool
  | .ok _ s => some (s.regs.bank_Bool .__tlb_enabled)
  | .error _ _ => none
theorem chunk0 (s : State) :
    tlb (initialize_registers_0 () s) = some (s.regs.bank_Bool .__tlb_enabled) := by rfl
#print axioms chunk0
end InitBoolProbe
