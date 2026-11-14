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

/- Literal source ImpDefBool branches, computed once by kernel reduction. -/
set_option maxRecDepth 8192 in
theorem impdef_prev_eret (s : SequentialState Regs oracleChoiceSource) :
    (__IMPDEF_boolean "SPE prev br on eret" : SailM Bool) s = .ok false s := by
  rfl
attribute [step_summary] impdef_prev_eret
#print axioms impdef_prev_eret

set_option maxRecDepth 8192 in
theorem impdef_prev_exception (s : SequentialState Regs oracleChoiceSource) :
    (__IMPDEF_boolean "SPE prev br on exception" : SailM Bool) s = .ok false s := by
  rfl
attribute [step_summary] impdef_prev_exception
#print axioms impdef_prev_exception

set_option maxRecDepth 8192 in
theorem impdef_prev_isb (s : SequentialState Regs oracleChoiceSource) :
    (__IMPDEF_boolean "SPE prev br on isb" : SailM Bool) s = .ok false s := by
  rfl
attribute [step_summary] impdef_prev_isb
#print axioms impdef_prev_isb

end NativeEntryCallerParts
