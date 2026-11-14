import Pilot.Driver
import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace S2WriteBytes
/- The runtime operation used by ordinary-RAM PhysMemWrite, before event framing. -/
drive_spec native, complete :
  fun (addr : Nat) (descriptor : BitVec 64)
      (s : SequentialState Regs oracleChoiceSource) =>
    (PreSail.writeBytes (n := 8) addr descriptor : SailM Bool) s
attribute [step_summary] complete
#print axioms complete
end S2WriteBytes
