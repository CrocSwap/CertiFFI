import DitShim243.StateAt
open Sail ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxCore CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
namespace DitShim243.StateShift

/-- Iteration composition, independent of whether any particular step succeeds. -/
theorem stateAt_add (real : Type) [Sail.SailReal real] (s : NativeState) (a : Nat) :
    ∀ b, stateAt real s (a + b) = stateAt real (stateAt real s a) b
  | 0 => rfl
  | b + 1 => by
    show next real (stateAt real s (a + b)) = next real (stateAt real (stateAt real s a) b)
    rw [stateAt_add real s a b]

#print axioms stateAt_add
end DitShim243.StateShift
