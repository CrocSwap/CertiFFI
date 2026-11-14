import Pilot.Driver
import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntry.IsbSy.Dispatch
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
/- GENERATED exact actual-model selector equations: register reads remain reads;
literal source constants remain constants. No generator-selected default. -/
set_option maxRecDepth 4096 in
@[step_summary] theorem impdef_selector0 (s : SequentialState Regs oracleChoiceSource) :
    (ImpDefBool "ISB generates Branch records" : SailM Bool) s =
      (readReg Register.__isb_is_branch : SailM Bool) s := by rfl
#print axioms impdef_selector0

set_option maxRecDepth 4096 in
@[step_summary] theorem impdef_selector1 (s : SequentialState Regs oracleChoiceSource) :
    (ImpDefBool "SPE prev br on eret" : SailM Bool) s =
      (pure false : SailM Bool) s := by rfl
#print axioms impdef_selector1

set_option maxRecDepth 4096 in
@[step_summary] theorem impdef_selector2 (s : SequentialState Regs oracleChoiceSource) :
    (ImpDefBool "SPE prev br on exception" : SailM Bool) s =
      (pure false : SailM Bool) s := by rfl
#print axioms impdef_selector2

set_option maxRecDepth 4096 in
@[step_summary] theorem impdef_selector3 (s : SequentialState Regs oracleChoiceSource) :
    (ImpDefBool "SPE prev br on isb" : SailM Bool) s =
      (pure false : SailM Bool) s := by rfl
#print axioms impdef_selector3
end NativeEntry.IsbSy.Dispatch
