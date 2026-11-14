import Pilot.UndefSummaries
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1POEnabled10
drive_spec native, complete :
  fun (s : SequentialState Regs oracleChoiceSource) =>
    AArch64_S1POEnabled .Regime_EL10 s
attribute [step_summary] complete
#print axioms complete
end S1POEnabled10
