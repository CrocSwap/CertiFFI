import Pilot.Driver
import Pilot.EvalProfile
import Pilot.UndefSummaries
import Pilot.NativeExport
import Pilot.GPRSummary
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions EvalProfile
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
namespace PF_Survey_57dab62365f7c401
drive_spec native, complete :
  fun (real : Type) [Sail.SailReal real] (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (N : BitVec 1) (shift : BitVec 2) (opc : BitVec 2) (sf : BitVec 1) (callerOpcode : BitVec 32) (callerSEE : Int) (s : SequentialState Regs oracleChoiceSource) =>
    decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf s
#print axioms complete
end PF_Survey_57dab62365f7c401
