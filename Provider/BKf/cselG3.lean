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
drive_spec cselG3_native, cselG3_complete :
  fun (real : Type) [Sail.SailReal real] (Rd Rn Rm : BitVec 5) (s : SequentialState Regs oracleChoiceSource) =>
    ((do let _ ← (decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 3#4 Rm 0#1 1#1 : SailM Unit);
         let u ← get
         pure (u.regs.gpr, u.regs.SP_EL0, u.regs._Z)) : SailM _) s
#print axioms cselG3_complete
end ArmBridge.BKf
