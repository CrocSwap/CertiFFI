import ReleaseProfile.GB10.HeapStaticInst

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

/-! Worked Heap normal positive C2: the Translate statics at the clean world (vendored HeapStaticInst) filled in;
only the three closed-membership atoms (Translate route B) remain explicit. -/

namespace ReleaseProfile.GB10.Heap.Normal

open ReleaseProfile.MachineSource ReleaseProfile.GB10 ReleaseProfile.GB10.Heap

variable (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)

#check "CURRENT_DECL GB10.Heap.Normal.ClosedAt"
/-- The closed-membership atom (122) at the world entry (F21: 272/273 are now world facts, HeapF21World). -/
structure ClosedAt (pcount : BitVec 88) {domain : ArmCert.Translate.Model.QueryDomain} (spec : ArmCert.Translate.Model.TopologyImageSpec domain) : Prop where
  a122 : CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/closed" (ArmCert.Translate.Model.ClosedMembershipAt spec (sourceAttributes rho caller) W.rows W.mapping (ArmBridge.CruxGenGuarded.Release.shimMap spec W.mapping W.base W.pins) (ArmBridge.CruxGenGuarded.beforeFetchState (E rho caller pcount)))

#check "CURRENT_DECL GB10.Heap.Normal.heap_normal_c2_of_closed"
theorem heap_normal_c2_of_closed (closed : ∀ (pcount : BitVec 88)
      (spec : ArmCert.Translate.Model.TopologyImageSpec
        (fun q => ∃ q0 ∈ HeapWorldTables.queries, ArmCertWalk.SamePage q0.va q.va)),
      SourceSpec rho caller spec → spec.layout = HeapWorldTables.tables.layout →
      spec.logicalRows = HeapWorldTables.tables.logicalRows →
      spec.imageRows = HeapWorldTables.tables.imageRows → ClosedAt rho caller pcount spec) :
    NormalC2 rho caller :=
  heap_normal_c2_of_statics rho caller fun pcount spec sspec hlay hlr hir =>
    have cl := closed pcount spec sspec hlay hlr hir
    {
      a20 := StaticInst.a20,
      a122 := cl.a122,
      a123 := StaticInst.a123 rho caller pcount,
      a244 := StaticInst.a244 hir,
      a256 := StaticInst.a256 rho caller pcount,
      a258 := StaticInst.a258 hir,
      a260 := StaticInst.a260 hir hlr,
      a262 := StaticInst.a262,
      a263 := StaticInst.a263 rho caller pcount,
      a267 := StaticInst.a267,
      a268 := StaticInst.a268
    }

end ReleaseProfile.GB10.Heap.Normal

#print axioms ReleaseProfile.GB10.Heap.Normal.heap_normal_c2_of_closed
