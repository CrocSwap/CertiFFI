import Pilot.UndefSummaries
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1LeafOutputPerms
drive_spec native, complete :
  fun (permissions : Permissions) (d : BitVec 64) (wp : S1TTWParams)
      (s : SequentialState Regs oracleChoiceSource) (hD128 : wp.d128 = 0#1) =>
    AArch64_S1ApplyOutputPerms permissions d .Regime_EL20 wp s
attribute [step_summary] complete
#print axioms complete
end S1LeafOutputPerms
