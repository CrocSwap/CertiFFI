import Pilot.S2Granule
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace S2Decode
drive_spec native, complete :
  fun (s : SequentialState Regs oracleChoiceSource) =>
    AArch64_S2DecodeTG0 0#2 s
attribute [step_summary] complete
#print axioms complete
end S2Decode
