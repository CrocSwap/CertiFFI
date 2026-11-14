import ReleaseProfile.GB10.HeapPort.Initial5C2Atoms
import ReleaseProfile.GB10.HeapVariantStatics

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192

/-! Heap Initial5 positive C2: reduction with the Translate static atoms at the variant
world (`HeapVariantStatics`, `WD d` with d = (V 32 0).data). -/

namespace ReleaseProfile.GB10.Heap.Trap.I5

open ReleaseProfile.MachineSource ReleaseProfile.GB10 ReleaseProfile.GB10.Heap ReleaseProfile.GB10.Heap.Trap

theorem statics5 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (pcount : BitVec 88)
    (spec : ArmCert.Translate.Model.TopologyImageSpec (fun q => ∃ q0 ∈ HeapWorldTables.queries, ArmCertWalk.SamePage q0.va q.va))
    (sspec : SourceSpec rho caller spec) (hlay : spec.layout = HeapWorldTables.tables.layout)
    (hlr : spec.logicalRows = HeapWorldTables.tables.logicalRows) (hir : spec.imageRows = HeapWorldTables.tables.imageRows) :
    TrapStaticsAt rho caller 32 0 pcount spec :=
  let d := (Variant.variantWorld 32 0).data
  { a20 := VariantStatics.a20 d
    a122 := VariantStatics.a122 rho caller d pcount rfl rfl rfl sspec hlay hlr hir
    a123 := VariantStatics.a123 rho caller d pcount
    a244 := VariantStatics.a244 d hir
    a256 := VariantStatics.a256 rho caller d pcount
    a258 := VariantStatics.a258 d hir
    a261 := VariantStatics.a261 d hir
    a262 := VariantStatics.a262 d
    a266 := VariantStatics.a266 rho caller d pcount
    a269 := VariantStatics.a269 rho caller d pcount
    a270 := VariantStatics.a270 d
    a274 := VariantStatics.a274 d hir }

#check "CURRENT_DECL GB10.Heap.Trap.I5.initial5_c2"
theorem initial5_c2 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) : Initial5C2 rho caller :=
  initial5_c2_of_statics rho caller (statics5 rho caller)

end ReleaseProfile.GB10.Heap.Trap.I5

#print axioms ReleaseProfile.GB10.Heap.Trap.I5.initial5_c2
