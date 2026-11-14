import Pilot.Driver
import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1LeafBase
drive_spec native, complete :
  fun (d : BitVec 64) (level : Int) (s : SequentialState Regs oracleChoiceSource) =>
    AArch64_LeafBase d 0#1 0#1 .TGx_4KB level s
attribute [step_summary] complete
#print axioms complete
end S1LeafBase
