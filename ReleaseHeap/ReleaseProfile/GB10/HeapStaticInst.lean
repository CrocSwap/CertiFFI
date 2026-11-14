import ReleaseProfile.GB10.HeapStaticAtoms
import ReleaseProfile.GB10.HeapC2Normal

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

/-!
# Heap normal C2 statics at the clean world

Each residual static field of `card_normal` (A2b indices) at `W := HeapWorldData.world`,
`E := worldEntry worldSemantics rho caller W pcount`, for any spec with `SourceSpec` and the world's tables.
-/

namespace ReleaseProfile.GB10.Heap.StaticInst

open ReleaseProfile.MachineSource ReleaseProfile.GB10 ReleaseProfile.GB10.Heap ReleaseProfile.GB10.Heap.Statics
open ArmCert.Translate ArmCert.Translate.Model

abbrev W := HeapWorldData.world

variable (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (pcount : BitVec 88)

abbrev E := worldEntry worldSemantics rho caller W pcount

theorem scopeIs : ScopeIs W HeapWorldData.shimOffsets := fun _ => Iff.rfl

/-- Image placement over any offset list covering the scope (the world's plan is code ++ shim). -/
theorem imageOn_world (offs : List Nat) (hin : ∀ o, W.scope o → o ∈ offs)
    (himg : W.imagePlan = HeapStatics.imagePlanOf offs W.image W.loadBase W.mapping)
    (chk : HeapStatics.checkImageDefined offs W.image W.loadBase W.mapping = true) :
    MemReloc.ImageOn W.scope W.image (E rho caller pcount) W.loadBase W.mapping :=
  imageOn_mono hin (HeapStatics.imageOn_of_imagePlan
    (himg ▸ fun a b m => world_realizes_image worldSemantics rho caller W pcount (a, b) m) chk)

theorem a20 : CertiFFI.Claim.DeploymentObligation "comp:caller:image-table-separated"
    (ArmCert.Translate.Model.ImageTableSeparated W.scope W.loadBase W.mapping (RtShim2.ShimMem.slotBytes W.pins W.mapping)) :=
  ⟨atom20 W scopeIs (n := (W.mapping (BitVec.ofNat 64 W.pins.sp)).getD 0) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)⟩

set_option maxRecDepth 200000 in
theorem a123 : CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/placed"
    (MemReloc.ImageOn W.scope W.image (E rho caller pcount) W.loadBase W.mapping) :=
  ⟨imageOn_world rho caller pcount (HeapV2StepCerts.codeOffsets ++ HeapWorldData.shimOffsets)
    (fun _ h => h.elim (fun h => List.mem_append.2 (Or.inr h)) (fun h => List.mem_append.2 (Or.inl h))) rfl
    (by decide +kernel)⟩

section spec

variable {domain : QueryDomain} {spec : TopologyImageSpec domain}

theorem a244 (hir : spec.imageRows = HeapWorldTables.tables.imageRows) :
    CertiFFI.Claim.DeploymentObligation "card:code-static"
      (RtDit.ShimFetch.ShimCodeStatic W.mapping W.base W.scope (ArmCert.Translate.Model.rowsFootprint spec.imageRows).byte) :=
  ⟨atom245 W scopeIs _ (by rw [hir]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

theorem a258 (hir : spec.imageRows = HeapWorldTables.tables.imageRows) :
    CertiFFI.Claim.DeploymentObligation "card:code-static"
      (RtShim.SlotPrem.ShimSlotStatic W.pins W.mapping (ArmCert.Translate.Model.rowsFootprint spec.imageRows)) :=
  ⟨atom259 spec W (by rw [hir]; decide +kernel)⟩

theorem cmap_agrees :
    ConsumerMapAgrees spec W.mapping (HeapV2StepCerts.E17General.cmap spec W.mapping W.base W.pins) := by
  apply HeapV2E17.consumer_agrees
  intro va acc size permitted
  rcases permitted with ⟨access, member, hva, _, _⟩ | ⟨code, member, hva, _, _⟩
  · subst hva; exact Normal.mapped_of (List.all_eq_true.1 Normal.world_data_mapped access member)
  · subst hva; exact Normal.mapped_of (List.all_eq_true.1 Normal.world_code_mapped code member)

theorem a260 (hir : spec.imageRows = HeapWorldTables.tables.imageRows)
    (hlr : spec.logicalRows = HeapWorldTables.tables.logicalRows) :
    CertiFFI.Claim.DeploymentObligation "card:body-entry/S" (NativeBodyDeploy.BodyStatic spec W.mapping W.base W.pins) :=
  ⟨atom261 spec W (by rw [hir]; decide +kernel) (by decide +kernel) (by decide +kernel)
    (by unfold HeapV2StepCerts.C3.DataStatic; rw [hir]; decide +kernel) (fun i => by unfold HeapV2E17.pin; split <;> decide) (by decide +kernel)
    (by decide +kernel) ⟨(W.mapping (RtSaved.slotVA W.pins)).getD 0, by decide +kernel⟩
    (by decide) (by decide) cmap_agrees (by rw [hlr]; decide +kernel)⟩

end spec

theorem a256 : CertiFFI.Claim.DeploymentObligation "card:slot-present"
    (RtShim.SlotPrem.ShimSlotPresent W.pins W.mapping (E rho caller pcount)) :=
  ⟨atom257 worldSemantics rho caller W pcount (by decide +kernel)⟩

theorem a262 : CertiFFI.Claim.DeploymentObligation "card:body-entry/hscope"
    (∀ (o : Nat), HeapV2StepCerts.codeScope o → W.scope o) :=
  ⟨atom263 W scopeIs⟩

theorem a263 : CertiFFI.Claim.DeploymentObligation "card:body-entry/presentE"
    (HeapV2StepCerts.C3.DataPresent W.pins W.mapping (E rho caller pcount)) :=
  ⟨atom264 worldSemantics rho caller W pcount (by decide +kernel)⟩

theorem a267 : CertiFFI.Claim.DeploymentObligation "comp:caller:image-table-separated"
    (ArmCert.Translate.Model.ImageTableSeparated W.scope W.base W.mapping (HeapV2StepCerts.Residue.StoreBytes W.pins W.mapping)) :=
  ⟨atom268 W scopeIs (by decide +kernel) (by decide +kernel)⟩

theorem a268 : CertiFFI.Claim.DeploymentObligation "card:default-slot-store-separation"
    (∀ (a : Nat), RtShim2.ShimMem.slotBytes W.pins W.mapping a → ¬HeapV2StepCerts.Residue.StoreBytes W.pins W.mapping a) :=
  ⟨atom269 W (by decide +kernel)⟩

end ReleaseProfile.GB10.Heap.StaticInst
#print axioms ReleaseProfile.GB10.Heap.StaticInst.a20
#print axioms ReleaseProfile.GB10.Heap.StaticInst.a123
#print axioms ReleaseProfile.GB10.Heap.StaticInst.a244
#print axioms ReleaseProfile.GB10.Heap.StaticInst.a256
#print axioms ReleaseProfile.GB10.Heap.StaticInst.a258
#print axioms ReleaseProfile.GB10.Heap.StaticInst.a260
#print axioms ReleaseProfile.GB10.Heap.StaticInst.a262
#print axioms ReleaseProfile.GB10.Heap.StaticInst.a263
#print axioms ReleaseProfile.GB10.Heap.StaticInst.a267
#print axioms ReleaseProfile.GB10.Heap.StaticInst.a268
