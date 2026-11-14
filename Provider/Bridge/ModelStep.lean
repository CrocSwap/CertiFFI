import Bridge.Boundary
import ArmFull.Fn.M0580
import ArmFull.Fn.M1475
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.Boundary

/-- The model instruction step: VERBATIM upstream
`step_model` (sail-upstream arm-v9.4-a src/elfmain.sail:53):
  `function step_model() = { SEE = -1; __TopLevel(); __CycleEnd(); }`.
The frozen Lean translation omits this harness function; it is not a model change. -/
def modelStep (real : Type) [Sail.SailReal real] : SailM Unit := do
  writeReg SEE (-1)
  __TopLevel (real := real) ()
  __CycleEnd ()

end ArmBridge.Boundary
