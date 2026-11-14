import NativeEntryCallerParts.Gcs
import Pilot.Driver
import Pilot.EvalProfile
import Pilot.UndefSummaries
import Pilot.NativeExport
import Pilot.GPRSummary
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryCallerParts
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
/- Exact actual caller prefix with BranchTo left as its original continuation.
   Compile using EVAL_OPAQUE_CALLEES=ArmFull.Functions.BranchTo.
   This is not a success theorem for the opaque BranchTo call. -/
drive_spec BlrPrefix_native, BlrPrefix_complete :
  fun (Rn : BitVec 5) (s : SequentialState Regs oracleChoiceSource)
      (el : s.regs.PSTATE.EL = 0#2)
      (gcsEn : _get_SCR_EL3_Type_GCSEn (s.regs.bank_BitVec_64 .SCR_EL3) = 0#1)
      (aa64 : s.regs.FeatureImpl[4] = true)
      (rn : Rn.toNat < 31)
    => (decode_blr_aarch64_instrs_branch_unconditional_register 0#5 Rn 0#1 0#1 1#2 0#1 : SailM Unit) s

#print axioms BlrPrefix_complete
end NativeEntryCallerParts
