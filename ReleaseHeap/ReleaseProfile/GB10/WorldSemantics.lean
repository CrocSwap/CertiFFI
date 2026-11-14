import ReleaseProfile.GB10.ModelEntry
import NativeMteTagCheck.Primitive

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024

/-!
# Registered model semantics constant (world-neutral)

TagStatusRows convention: the oracle answers 0 at every choice point, as in the old entry's
choice state. Semantics, not configuration. Shared by Heap and Runtime C2.
-/

namespace ReleaseProfile.GB10

open ReleaseProfile.MachineSource

#check "CURRENT_DECL GB10.zeroOracle"
def zeroOracle : Sail.ConcurrencyInterfaceV1.Oracle := fun _ p =>
  match p with
  | .bool => false
  | .bit => 0
  | .int => 0
  | .nat => 0
  | .string => ""
  | .fin _ => 0
  | .bitvector _ => 0

#check "CURRENT_DECL GB10.worldSemantics"
def worldSemantics : ModelSemantics := ⟨(zeroOracle, 0), ∅⟩

#check "CURRENT_DECL GB10.model_tagStatusRows"
theorem model_tagStatusRows (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (payload : ModelPayload) (draws : Nat) :
    NativeMteTagCheck.TagStatusRows (makeModelEntry worldSemantics rho caller payload)
      ((makeModelEntry worldSemantics rho caller payload).choiceOcc.getD 1354 0) draws := by
  intro index within
  rfl

end ReleaseProfile.GB10

#print axioms ReleaseProfile.GB10.model_tagStatusRows
