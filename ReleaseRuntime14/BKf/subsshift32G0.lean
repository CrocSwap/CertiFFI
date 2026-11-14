import Pilot.Driver
import Pilot.EvalProfile
import Pilot.UndefSummaries
import Pilot.NativeExport
import Pilot.GPRSummary
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions EvalProfile
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option linter.unusedVariables false
namespace ArmBridge.BKf
drive_spec subsshift32G0_native, subsshift32G0_complete :
  fun (real : Type) [Sail.SailReal real] (Rd Rn Rm : BitVec 5) (s : SequentialState Regs oracleChoiceSource) =>
    ((do let _ ← (decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn 0#6 Rm 0#2 1#1 1#1 0#1 : SailM Unit);
         let u ← get
         pure (u.regs.gpr, u.regs.SP_EL0, u.regs._Z, u.regs.PSTATE.N, u.regs.PSTATE.Z, u.regs.PSTATE.C, u.regs.PSTATE.V)) : SailM _) s
#print axioms subsshift32G0_complete
end ArmBridge.BKf
