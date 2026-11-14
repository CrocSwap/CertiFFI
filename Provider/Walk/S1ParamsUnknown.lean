import Pilot.Driver
import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1ParamsUnknown
drive_spec native, complete :
  fun (label : ChoiceLabel) (s : SequentialState Regs oracleChoiceSource) =>
    undefined_S1TTWParams label () s
attribute [step_summary] complete
#print axioms complete
end S1ParamsUnknown
