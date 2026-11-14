import Pilot.Driver
import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace S2UndefAddress
drive_spec native, complete :
  fun (label : ChoiceLabel) (s : SequentialState Regs oracleChoiceSource) =>
    undefined_FullAddress label () s
attribute [step_summary] complete
#print axioms complete
end S2UndefAddress
