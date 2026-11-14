import Pilot.Driver
import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace S2SecurityEL
drive_spec native, complete :
  fun (el : BitVec 2) (s : SequentialState Regs oracleChoiceSource)
      (hNoRME : s.regs.FeatureImpl[232] = false) => SecurityStateAtEL el s
attribute [step_summary] complete
#print axioms complete
end S2SecurityEL
