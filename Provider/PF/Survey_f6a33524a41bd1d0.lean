import Pilot.Driver
import Pilot.EvalProfile
import Pilot.UndefSummaries
import Pilot.NativeExport
import Pilot.GPRSummary
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions EvalProfile
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
namespace PF_Survey_f6a33524a41bd1d0
drive_spec native, complete :
  fun (real : Type) [Sail.SailReal real] (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (shift : BitVec 2) (S : BitVec 1) (op : BitVec 1) (sf : BitVec 1) (callerOpcode : BitVec 32) (callerSEE : Int) (s : SequentialState Regs oracleChoiceSource) =>
    decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op sf s
#print axioms complete
end PF_Survey_f6a33524a41bd1d0
