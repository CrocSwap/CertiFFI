import ReleaseProfile.GB10.HeapC2NormalFinal
import ReleaseProfile.GB10.HeapClosedB

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

/-!
# Worked Heap normal positive C2

For every admissible source completion and admitted caller, there is a source-pinned spec and a
source-built model entry (registers = the canonical source register file, with the clean Heap world's
data part and memory) satisfying every retained original input of the worked Heap normal card.
No configuration is chosen by the model: the entry agrees with the canonical source configuration.
-/

namespace ReleaseProfile.GB10.Heap.Normal

open ReleaseProfile.MachineSource ReleaseProfile.GB10 ReleaseProfile.GB10.Heap

#check "CURRENT_DECL GB10.Heap.Normal.heap_normal_c2"
/-- Positive C2 for the worked Heap normal card. -/
theorem heap_normal_c2 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) : NormalC2 rho caller :=
  heap_normal_c2_of_closed rho caller fun pcount _spec sspec hlay hlr hir =>
    ⟨HeapClosedB.a122 rho caller pcount sspec hlay hlr hir⟩

end ReleaseProfile.GB10.Heap.Normal

#print axioms ReleaseProfile.GB10.Heap.Normal.heap_normal_c2
