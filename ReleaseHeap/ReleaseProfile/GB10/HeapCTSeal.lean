import ReleaseProfile.GB10.HeapPort.CTC2Atoms
import ReleaseProfile.GB10.HeapStaticInst
import ReleaseProfile.GB10.HeapClosedB

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

/-!
# Worked Heap CT positive C2

For every admissible source completion and admitted CT caller pair, there is one source-pinned spec (first
caller) and two source-built model entries (one per caller, same clean world data) satisfying every retained
original input of the worked Heap CT card. No configuration is chosen by the model.
-/

namespace ReleaseProfile.GB10.Heap.CT

open ReleaseProfile.MachineSource ReleaseProfile.GB10 ReleaseProfile.GB10.Heap ReleaseProfile.GB10.Heap.Normal

#check "CURRENT_DECL GB10.Heap.CT.heap_ct_c2"
/-- Positive C2 for the worked Heap CT card. -/
theorem heap_ct_c2 (rho : AdmissibleSourceCompletion) (callers : AdmissibleCTCallers rho) : CTC2 rho callers :=
  heap_ct_c2_of_statics rho callers fun caller pcount _spec sspec hlay hlr hir =>
    { a20 := StaticInst.a20
      a122 := HeapClosedB.a122 rho caller pcount sspec hlay hlr hir
      a123 := StaticInst.a123 rho caller pcount
      a244 := StaticInst.a244 hir
      a256 := StaticInst.a256 rho caller pcount
      a258 := StaticInst.a258 hir
      a260 := StaticInst.a260 hir hlr
      a262 := StaticInst.a262
      a263 := StaticInst.a263 rho caller pcount
      a267 := StaticInst.a267
      a268 := StaticInst.a268
      a272 := HeapClosedB.a272 rho sspec hlay hlr hir
      a273 := HeapClosedB.a273 rho sspec hlay hlr hir }

end ReleaseProfile.GB10.Heap.CT

#print axioms ReleaseProfile.GB10.Heap.CT.heap_ct_c2
