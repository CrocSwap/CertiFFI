import Pilot.Driver
import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1MAIRAttr
drive_spec native, complete :
  fun (index : Int) (mair2 mair : BitVec 64) (s : SequentialState Regs oracleChoiceSource) =>
    AArch64_MAIRAttr index mair2 mair s
attribute [step_summary] complete
#print axioms complete
end S1MAIRAttr
