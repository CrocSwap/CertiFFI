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
drive_spec subsimmG0_native, subsimmG0_complete :
  fun (real : Type) [Sail.SailReal real] (Rd Rn : BitVec 5) (imm12 : BitVec 12) (s : SequentialState Regs oracleChoiceSource) =>
    ((do let _ ← (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 1#1 1#1 1#1 : SailM Unit);
         let u ← get
         pure (u.regs.gpr, u.regs.SP_EL0, u.regs._Z, u.regs.PSTATE.N, u.regs.PSTATE.Z, u.regs.PSTATE.C, u.regs.PSTATE.V)) : SailM _) s
#print axioms subsimmG0_complete
end ArmBridge.BKf
