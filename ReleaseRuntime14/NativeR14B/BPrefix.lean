import NativeEntryCallerParts.Gcs
import Pilot.Driver
import Pilot.EvalProfile
import Pilot.UndefSummaries
import Pilot.NativeExport
import Pilot.GPRSummary
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeR14B
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
/- Exact actual B (unconditional immediate) prefix with BranchTo left as its original continuation.
   Compile using EVAL_OPAQUE_CALLEES=ArmFull.Functions.BranchTo. Not a success theorem for BranchTo. -/
drive_spec BPrefix_native, BPrefix_complete :
  fun (imm26 : BitVec 26) (s : SequentialState Regs oracleChoiceSource)
    => (decode_b_uncond_aarch64_instrs_branch_unconditional_immediate imm26 0#1 : SailM Unit) s

set_option pp.proofs true in
#print BPrefix_native
#print axioms BPrefix_complete
end NativeR14B
