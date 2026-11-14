import Pilot.Driver
import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1NextTableBase
/- Parameter-local 4 KiB, non-DS, 64-bit descriptor component. The caller must
   derive these walk parameters from its named hardware profile. -/
drive_spec native, complete :
  fun (descriptor : BitVec 64) (s : SequentialState Regs oracleChoiceSource) =>
    AArch64_NextTableBase descriptor 0#1 0#1 .TGx_4KB s
attribute [step_summary] complete
#print axioms complete
end S1NextTableBase
