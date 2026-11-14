import Pilot.Driver
import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace S2Granule
drive_spec native, complete :
  fun (tg : TGx) (s : SequentialState Regs oracleChoiceSource) =>
    AArch64_HaveS2TG tg s
attribute [step_summary] complete
#print axioms complete
end S2Granule
