import Pilot.Driver
import Pilot.EvalProfile
import Pilot.UndefSummaries
import Pilot.NativeExport
import Pilot.GPRSummary
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions EvalProfile
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
namespace PF_Survey_ffe4e35910ac1dda
drive_spec native, complete :
  fun (real : Type) [Sail.SailReal real] (Rd : BitVec 5) (Rn : BitVec 5) (o2 : BitVec 1) (cond : BitVec 4) (Rm : BitVec 5) (op : BitVec 1) (sf : BitVec 1) (callerOpcode : BitVec 32) (callerSEE : Int) (s : SequentialState Regs oracleChoiceSource) =>
    decode_csel_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op sf s
#print axioms complete
end PF_Survey_ffe4e35910ac1dda
