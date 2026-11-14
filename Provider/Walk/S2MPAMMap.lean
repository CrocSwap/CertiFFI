import Pilot.Driver
import Walk.S2MapVPM
import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace S2MPAMMap
drive_spec native, complete :
  fun (v : BitVec 16) (s : SequentialState Regs oracleChoiceSource) => MAP_vPARTID v s
attribute [step_summary] complete
#print axioms complete
end S2MPAMMap
