import Pilot.Driver
import Pilot.EvalProfile
import Pilot.UndefSummaries
import Pilot.NativeExport
import Pilot.GPRSummary
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions EvalProfile
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
namespace PF_Survey_6091d9feb3c7f2e3
drive_spec native, complete :
  fun (real : Type) [Sail.SailReal real] (Rd : BitVec 5) (Rn : BitVec 5) (imms : BitVec 6) (immr : BitVec 6) (N : BitVec 1) (opc : BitVec 2) (sf : BitVec 1) (callerOpcode : BitVec 32) (callerSEE : Int) (s : SequentialState Regs oracleChoiceSource) =>
    decode_ands_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr N opc sf s
#print axioms complete
end PF_Survey_6091d9feb3c7f2e3
