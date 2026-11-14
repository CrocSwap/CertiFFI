import Pilot.Driver
import Walk.S1EL2Enabled
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace GetGuestSCTLR2
abbrev State := SequentialState Regs oracleChoiceSource
drive_spec native, complete : fun (s : State) => IsSCTLR2EL2Enabled () s
attribute [step_summary] complete
theorem function_eq : IsSCTLR2EL2Enabled = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms complete
#print axioms function_eq
end GetGuestSCTLR2
