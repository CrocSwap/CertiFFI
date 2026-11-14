import Walk.S1TCREnabled
import Walk.S1EL2Enabled
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace GetGuestTCR2
abbrev State := SequentialState Regs oracleChoiceSource
/- All-state controls: feature vector, SCR/HCRX and oracle remain symbolic. -/
drive_spec native, complete : fun (s : State) => IsTCR2EL1Enabled () s
attribute [step_summary] complete
#print axioms complete
theorem function_eq : IsTCR2EL1Enabled = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms function_eq
end GetGuestTCR2

