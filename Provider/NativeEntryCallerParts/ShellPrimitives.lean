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

drive_spec using32_native, using32_complete :
  fun (s : SequentialState Regs oracleChoiceSource)
      (f4 : s.regs.FeatureImpl[4]! = true)
      (nrw : s.regs.PSTATE.nRW = 0#1)
    => (UsingAArch32 () : SailM Bool) s
#print axioms using32_complete

drive_spec brbe_native, brbe_complete :
  fun (s : SequentialState Regs oracleChoiceSource)
      (brbe : s.regs.FeatureImpl[230]! = false)
    => (HaveBRBExt () : SailM Bool) s
#print axioms brbe_complete

drive_spec haveSpe_native, haveSpe_complete :
  fun (s : SequentialState Regs oracleChoiceSource)
    => (HaveStatisticalProfiling () : SailM Bool) s
#print axioms haveSpe_complete

end NativeEntryCallerParts
