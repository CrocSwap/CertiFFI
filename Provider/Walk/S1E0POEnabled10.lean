import Pilot.UndefSummaries
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1E0POEnabled10
drive_spec native, complete :
  fun (nv1 : BitVec 1) (s : SequentialState Regs oracleChoiceSource) =>
    AArch64_S1E0POEnabled .Regime_EL10 nv1 s
attribute [step_summary] complete
#print axioms complete
end S1E0POEnabled10
