import Pilot.Driver
import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
namespace S2PAMax
/- The implementation's supported size is named, never read from a guessed
   architectural ID word. Invalid implementation sizes retain the source error. -/
drive_spec native, complete :
  fun (paSize : Int) (s : SequentialState Regs oracleChoiceSource)
      (hPA : s.regs.bank_Int .__supported_pa_size = paSize) =>
    AArch64_PAMax () s
attribute [step_summary] complete
#print axioms complete
end S2PAMax
