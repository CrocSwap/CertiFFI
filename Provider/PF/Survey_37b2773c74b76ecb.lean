import Pilot.Driver
import Pilot.EvalProfile
import Pilot.UndefSummaries
import Pilot.NativeExport
import Pilot.GPRSummary
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions EvalProfile
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
namespace PF_Survey_37b2773c74b76ecb
drive_spec native, complete :
  fun (real : Type) [Sail.SailReal real] (Rd : BitVec 5) (Rn : BitVec 5) (imm12 : BitVec 12) (sh : BitVec 1) (S : BitVec 1) (op : BitVec 1) (sf : BitVec 1) (callerOpcode : BitVec 32) (callerSEE : Int) (s : SequentialState Regs oracleChoiceSource) =>
    decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op sf s
#print axioms complete
end PF_Survey_37b2773c74b76ecb
