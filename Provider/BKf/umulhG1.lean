import Pilot.Driver
import Pilot.EvalProfile
import Pilot.UndefSummaries
import Pilot.NativeExport
import Pilot.GPRSummary
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions EvalProfile
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
namespace ArmBridge.BKf
drive_spec umulhG1_native, umulhG1_complete :
  fun (real : Type) [Sail.SailReal real] (Rd Rn Ra Rm : BitVec 5) (s : SequentialState Regs oracleChoiceSource) =>
    ((do let _ ← (decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit);
         let u ← get
         pure (u.regs.gpr, u.regs.SP_EL0, u.regs._Z)) : SailM _) s
#print axioms umulhG1_complete
end ArmBridge.BKf
