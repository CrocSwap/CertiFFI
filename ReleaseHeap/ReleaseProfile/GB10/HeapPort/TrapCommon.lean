import ReleaseProfile.GB10.HeapC2World
import ReleaseProfile.GB10.HeapC2Variant

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192

/-! Shared atoms for the Heap trap families (initial_k / ct_k) at the clean world variant.
Program/memory/tables are the clean world; atoms shared with normal use normal/variant lemmas; the
Translate static atoms are the `TrapStaticsAt` hypothesis (same role as Normal.StaticsAt). -/

namespace ReleaseProfile.GB10.Heap.Trap

open ReleaseProfile.MachineSource ReleaseProfile.GB10 ReleaseProfile.GB10.Heap ReleaseProfile.GB10.Heap.Normal ReleaseProfile.GB10.Heap.Variant

/-- Table rows for the body-entry plan: the clean world table plan. -/
abbrev trapTableRows : NativeSourceInit.Plan := ArmCert.Translate.Model.imageRowsPlan HeapWorldTables.imageRows

variable (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (x2 x3 : BitVec 64) (pcount : BitVec 88)

#check "CURRENT_DECL GB10.Heap.Trap.TrapStaticsAt"
/-- Translate-owned static atoms of a trap family at the variant entry (exact residual fields). -/
structure TrapStaticsAt {domain : ArmCert.Translate.Model.QueryDomain} (spec : ArmCert.Translate.Model.TopologyImageSpec domain) : Prop where
  a20 : CertiFFI.Claim.DeploymentObligation "comp:caller:image-table-separated" (ArmCert.Translate.Model.ImageTableSeparated (V x2 x3).scope (V x2 x3).loadBase (V x2 x3).mapping (RtShim2.ShimMem.slotBytes (V x2 x3).pins (V x2 x3).mapping))
  a122 : CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/closed" (ArmCert.Translate.Model.ClosedMembershipAt spec (sourceAttributes rho caller) (V x2 x3).rows (V x2 x3).mapping (ArmBridge.CruxGenGuarded.Release.shimMap spec (V x2 x3).mapping (V x2 x3).base (V x2 x3).pins) (ArmBridge.CruxGenGuarded.beforeFetchState (EV rho caller x2 x3 pcount)))
  a123 : CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/placed" (MemReloc.ImageOn (V x2 x3).scope (V x2 x3).image (EV rho caller x2 x3 pcount) (V x2 x3).loadBase (V x2 x3).mapping)
  a244 : CertiFFI.Claim.DeploymentObligation "card:code-static" (RtDit.ShimFetch.ShimCodeStatic (V x2 x3).mapping (V x2 x3).base (V x2 x3).scope (ArmCert.Translate.Model.rowsFootprint spec.imageRows).byte)
  a256 : CertiFFI.Claim.DeploymentObligation "card:slot-present" (RtShim.SlotPrem.ShimSlotPresent (V x2 x3).pins (V x2 x3).mapping (EV rho caller x2 x3 pcount))
  a258 : CertiFFI.Claim.DeploymentObligation "card:code-static" (RtShim.SlotPrem.ShimSlotStatic (V x2 x3).pins (V x2 x3).mapping (ArmCert.Translate.Model.rowsFootprint spec.imageRows))
  a261 : CertiFFI.Claim.DeploymentObligation "card:body-entry/static" (HeapV2StepCerts.CodeStatic (V x2 x3).mapping (V x2 x3).base (ArmCert.Translate.Model.rowsFootprint spec.imageRows).byte)
  a262 : CertiFFI.Claim.DeploymentObligation "card:body-entry/agrees" (ArmCert.Translate.Model.ConsumerMapAgrees spec (V x2 x3).mapping (ArmCert.Translate.Model.HeapV2E17.consumerMapOn (fun x => True) (V x2 x3).pins (V x2 x3).base.toNat (V x2 x3).mapping (ArmCert.Translate.Model.rowsFootprint spec.imageRows).byte))
  a266 : CertiFFI.Claim.DeploymentObligation "card:body-entry/presentE" (HeapV2StepCerts.C3.DataPresent (V x2 x3).pins (V x2 x3).mapping (EV rho caller x2 x3 pcount))
  a269 : CertiFFI.Claim.DeploymentObligation "card:body-entry/satE" (NativeSourceInit.Satisfies (ArmCert.Translate.Model.HeapV2.entryPlan (V x2 x3).base (V x2 x3).mapping HeapV2StepCerts.codeOffsets trapTableRows) (EV rho caller x2 x3 pcount).mem)
  a270 : CertiFFI.Claim.DeploymentObligation "card:body-entry/planAvoidsSlot" (∀ (row : NativeSourceInit.PhysicalByte), row ∈ ArmCert.Translate.Model.HeapV2.entryPlan (V x2 x3).base (V x2 x3).mapping HeapV2StepCerts.codeOffsets trapTableRows → ¬RtShim2.ShimMem.slotBytes (V x2 x3).pins (V x2 x3).mapping row.fst)
  a274 : CertiFFI.Claim.DeploymentObligation "card:body-entry/declared" (ArmCert.Translate.Model.PermissionRowsDeclared (V x2 x3).rows spec.imageRows)

theorem a263 : CertiFFI.Claim.DeploymentObligation "card:body-entry/page" ((V x2 x3).base.toNat % 4096 = 0) :=
  ⟨by show HeapWorldData.base.toNat % 4096 = 0; decide⟩
theorem a264b : CertiFFI.Claim.DeploymentObligation "card:body-entry/low" ((V x2 x3).base.toNat < 2 ^ 54) :=
  ⟨by show HeapWorldData.base.toNat < 2 ^ 54; decide⟩
theorem a271 : CertiFFI.Claim.DeploymentObligation "card:body-entry/codeMapped"
    (∀ (o : Nat), o ∈ HeapV2StepCerts.codeOffsets → ∃ pa, (V x2 x3).mapping (MemReloc.imageAddress (V x2 x3).base o) = some pa) := by
  refine ⟨fun o h => ?_⟩
  have c : HeapV2StepCerts.codeOffsets.all (fun o => (HeapWorldData.mapping (MemReloc.imageAddress HeapWorldData.base o)).isSome) = true := by decide +kernel
  exact Option.isSome_iff_exists.1 (List.all_eq_true.1 c o h)
theorem a272 : CertiFFI.Claim.DeploymentObligation "card:body-entry/codePresent"
    (∀ (o : Nat), o ∈ HeapV2StepCerts.codeOffsets → ∃ byte, ArmCert.Translate.Model.HeapV2.image (V x2 x3).base o = some byte) := by
  refine ⟨fun o h => ?_⟩
  have c : HeapV2StepCerts.codeOffsets.all (fun o => (ArmCert.Translate.Model.HeapV2.image HeapWorldData.base o).isSome) = true := by decide +kernel
  exact Option.isSome_iff_exists.1 (List.all_eq_true.1 c o h)
theorem a273 {domain : ArmCert.Translate.Model.QueryDomain} (spec : ArmCert.Translate.Model.TopologyImageSpec domain)
    (hir : spec.imageRows = HeapWorldTables.tables.imageRows) : CertiFFI.Claim.DeploymentObligation "card:body-entry/tables" (∀ (row : NativeSourceInit.PhysicalByte), row ∈ ArmCert.Translate.Model.imageRowsPlan spec.imageRows → row ∈ trapTableRows) :=
  ⟨fun row h => by rw [hir] at h; exact h⟩
theorem a275 {domain : ArmCert.Translate.Model.QueryDomain} (spec : ArmCert.Translate.Model.TopologyImageSpec domain)
    (hlr : spec.logicalRows = HeapWorldTables.tables.logicalRows) : CertiFFI.Claim.DeploymentObligation "E34" ((List.map (fun x => x.logical) spec.logicalRows).Nodup) :=
  ⟨by rw [hlr]; decide⟩
theorem a243T : CertiFFI.Claim.DeploymentObligation "card:default-trap-initial-tag-status-row" (NativeMteTagCheck.TagStatusRows (EV rho caller x2 x3 pcount) ((EV rho caller x2 x3 pcount).choiceOcc.getD 1354 0) 1) :=
  ⟨fun index h => (Variant.a243 rho caller x2 x3 pcount).holds index (by omega)⟩

end ReleaseProfile.GB10.Heap.Trap
