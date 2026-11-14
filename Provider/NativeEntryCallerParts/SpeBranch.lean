import NativeEntryCallerParts.SpeLiterals
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

/- Current primitive fields only; source control production remains open. -/
/- After specializing the three source string branches, the measured
   residual reaches 3367 evaluator heads at 100k; bound this declaration only. -/
set_option maxHeartbeats 400000 in
drive_spec spe_native, spe_complete :
  fun (target : BitVec 64) (branch : BranchType) (conditional : Bool) (s : SequentialState Regs oracleChoiceSource)
      (f4 : s.regs.FeatureImpl[4]! = true)
      (f2 : s.regs.FeatureImpl[2]! = false)
      (f3 : s.regs.FeatureImpl[3]! = false)
      (f6 : s.regs.FeatureImpl[6]! = true)
      (f7 : s.regs.FeatureImpl[7]! = true)
      (rme : s.regs.FeatureImpl[232]! = false)
      (vhe : s.regs.FeatureImpl[54]! = true)
      (brbe : s.regs.FeatureImpl[230]! = false)
      (el : s.regs.PSTATE.EL = 0#2)
      (nrw : s.regs.PSTATE.nRW = 0#1)
      (e2h : _get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1)
      (tge : _get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1)
      (ns : _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1)
      (pmb : _get_PMBLIMITR_EL1_Type_E (s.regs.bank_BitVec_64 .PMBLIMITR_EL1) = 0#1)
      (spe : s.regs.bank_Bool .SPESampleInFlight = false)
      (pmbs : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 .PMBSR_EL1) 17 17 = 0#1)
      (nspb : _get_MDCR_EL3_Type_NSPB (s.regs.bank_BitVec_64 .MDCR_EL3) = 3#2)
      (nspbe : _get_MDCR_EL3_Type_NSPBE (s.regs.bank_BitVec_64 .MDCR_EL3) = 0#1)
    => ((do
         SPEBranch target branch conditional true) : SailM _) s

attribute [step_summary] spe_complete
#print axioms spe_complete
end NativeEntryCallerParts
