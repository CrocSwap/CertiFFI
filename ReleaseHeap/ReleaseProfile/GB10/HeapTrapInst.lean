import ReleaseProfile.GB10.HeapTrapWorld
import ReleaseProfile.GB10.HeapInitialStatics

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

/-!
# Heap trap-family statics at the trap worlds

The Translate-owned non-closed static atoms of `card_initial_t` (tele-all indices 20, 123, 245, 257, 259,
262-265, 267, 270-276) at `Wt := HeapTrapWorld.world t`, `Et := worldEntry worldSemantics rho caller Wt pcount`,
`tableRows := Wt.tablePlan`, for every t : Fin 6 and any caller. Finite checks are decided once for all t.
-/

namespace ReleaseProfile.GB10.Heap.TrapInst

open ReleaseProfile.MachineSource ReleaseProfile.GB10 ReleaseProfile.GB10.Heap ReleaseProfile.GB10.Heap.Statics
open ArmCert.Translate ArmCert.Translate.Model ReleaseProfile.GB10.HeapTrapWorld

abbrev Wt (t : T) : HeapWorld := HeapTrapWorld.world t

abbrev Et (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (t : T) (pcount : BitVec 88) :=
  worldEntry worldSemantics rho caller (Wt t) pcount

theorem scopeIs (t : T) : ScopeIs (Wt t) HeapWorldData.shimOffsets := fun _ => Iff.rfl

/-! ### Finite checks, decided for all six worlds -/

theorem chk_sp : ∀ t : T, (Wt t).mapping (BitVec.ofNat 64 (Wt t).pins.sp) =
    some (((Wt t).mapping (BitVec.ofNat 64 (Wt t).pins.sp)).getD 0) := by decide +kernel
theorem chk_avoid_shim : ∀ t : T, HeapStatics.offsetsAvoid HeapWorldData.shimOffsets (Wt t).loadBase (Wt t).mapping
    (((Wt t).mapping (BitVec.ofNat 64 (Wt t).pins.sp)).getD 0) 16 = true := by decide +kernel
theorem chk_avoid_code : ∀ t : T, HeapStatics.offsetsAvoid HeapV2StepCerts.codeOffsets (Wt t).loadBase (Wt t).mapping
    (((Wt t).mapping (BitVec.ofNat 64 (Wt t).pins.sp)).getD 0) 16 = true := by decide +kernel
theorem chk_image : HeapStatics.checkImageDefined (HeapV2StepCerts.codeOffsets ++ HeapWorldData.shimOffsets)
    (HeapV2.image base) base mapping = true := by decide +kernel
theorem chk_slot : ∀ t : T, HeapStatics.checkSlotPresent (Wt t).pins (Wt t).mapping (Wt t).slotPlan = true := by
  decide +kernel
theorem chk_data : ∀ t : T, HeapStatics.checkDataPresent (Wt t).pins (Wt t).mapping (Wt t).dataPlan = true := by
  decide +kernel
theorem chk_planAvoids : ∀ t : T, InitialStatics.checkPlanAvoidsSlot
    (HeapV2.entryPlan (Wt t).base (Wt t).mapping HeapV2StepCerts.codeOffsets (Wt t).tablePlan) (Wt t).pins (Wt t).mapping = true := by
  decide +kernel
theorem chk_code_mapped : HeapV2Plan.codeWords.all
    (fun c => Normal.mappedB mapping (HeapV2E17.codeVA base.toNat c.1)) = true := by decide +kernel

variable (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (t : T) (pcount : BitVec 88)

theorem a20 : CertiFFI.Claim.DeploymentObligation "comp:caller:image-table-separated"
    (ImageTableSeparated (Wt t).scope (Wt t).loadBase (Wt t).mapping (RtShim2.ShimMem.slotBytes (Wt t).pins (Wt t).mapping)) :=
  ⟨atom20 (Wt t) (scopeIs t) (chk_sp t) (chk_avoid_shim t) (chk_avoid_code t)⟩

theorem a123 : CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/placed"
    (MemReloc.ImageOn (Wt t).scope (Wt t).image (Et rho caller t pcount) (Wt t).loadBase (Wt t).mapping) :=
  ⟨imageOn_mono (fun _ h => h.elim (fun h => List.mem_append.2 (Or.inr h)) (fun h => List.mem_append.2 (Or.inl h)))
    (HeapStatics.imageOn_of_imagePlan
      (fun a b m => world_realizes_image worldSemantics rho caller (Wt t) pcount (a, b)
        ((world_imagePlan t).symm ▸ m)) chk_image)⟩

theorem a257 : CertiFFI.Claim.DeploymentObligation "card:slot-present"
    (RtShim.SlotPrem.ShimSlotPresent (Wt t).pins (Wt t).mapping (Et rho caller t pcount)) :=
  ⟨atom257 worldSemantics rho caller (Wt t) pcount (chk_slot t)⟩

theorem a267 : CertiFFI.Claim.DeploymentObligation "card:body-entry/presentE"
    (HeapV2StepCerts.C3.DataPresent (Wt t).pins (Wt t).mapping (Et rho caller t pcount)) :=
  ⟨atom264 worldSemantics rho caller (Wt t) pcount (chk_data t)⟩

theorem a270 : CertiFFI.Claim.DeploymentObligation "card:body-entry/satE"
    (NativeSourceInit.Satisfies (HeapV2.entryPlan (Wt t).base (Wt t).mapping HeapV2StepCerts.codeOffsets (Wt t).tablePlan)
      (Et rho caller t pcount).mem) :=
  ⟨InitialStatics.satE_world worldSemantics rho caller (Wt t) pcount (world_imagePlan t)⟩

theorem a271 : CertiFFI.Claim.DeploymentObligation "card:body-entry/planAvoidsSlot"
    (∀ (row : NativeSourceInit.PhysicalByte),
      row ∈ HeapV2.entryPlan (Wt t).base (Wt t).mapping HeapV2StepCerts.codeOffsets (Wt t).tablePlan →
        ¬RtShim2.ShimMem.slotBytes (Wt t).pins (Wt t).mapping row.fst) :=
  ⟨InitialStatics.planAvoidsSlot_of_check (chk_planAvoids t)⟩

theorem a264 : CertiFFI.Claim.DeploymentObligation "card:body-entry/page" ((Wt t).base.toNat % 4096 = 0) :=
  ⟨show base.toNat % 4096 = 0 from by decide⟩

theorem a265 : CertiFFI.Claim.DeploymentObligation "card:body-entry/low" ((Wt t).base.toNat < 2 ^ 54) :=
  ⟨show base.toNat < 2 ^ 54 from by decide⟩

theorem a272 : CertiFFI.Claim.DeploymentObligation "card:body-entry/codeMapped"
    (∀ (o : Nat), o ∈ HeapV2StepCerts.codeOffsets → ∃ pa, (Wt t).mapping (MemReloc.imageAddress (Wt t).base o) = some pa) := by
  refine ⟨fun o ho => Option.isSome_iff_exists.1 ?_⟩
  have h : HeapV2StepCerts.codeOffsets.all (fun o => (mapping (MemReloc.imageAddress base o)).isSome) = true := by
    decide +kernel
  exact List.all_eq_true.1 h o ho

theorem a273 : CertiFFI.Claim.DeploymentObligation "card:body-entry/codePresent"
    (∀ (o : Nat), o ∈ HeapV2StepCerts.codeOffsets → ∃ byte, HeapV2.image (Wt t).base o = some byte) := by
  refine ⟨fun o ho => Option.isSome_iff_exists.1 ?_⟩
  have h : HeapV2StepCerts.codeOffsets.all (fun o => (HeapV2.image base o).isSome) = true := by decide +kernel
  exact List.all_eq_true.1 h o ho

section spec

variable {domain : QueryDomain} {spec : TopologyImageSpec domain}

theorem a245 (hir : spec.imageRows = HeapTrapTables.tables.imageRows) :
    CertiFFI.Claim.DeploymentObligation "card:code-static"
      (RtDit.ShimFetch.ShimCodeStatic (Wt t).mapping (Wt t).base (Wt t).scope (rowsFootprint spec.imageRows).byte) := by
  have c1 : checkImageTableSeparated base mapping (HeapWorldData.shimOffsets ++ HeapV2StepCerts.codeOffsets)
      (rowsFootprint HeapTrapTables.imageRows) = true := by decide +kernel
  have c2 : HeapV2ShimPlan.codeWords.all (fun c => checkImageWordContiguous mapping base (HeapV2ShimPlan.shimOffset + c.1)) = true := by
    decide +kernel
  have c3 : HeapV2ShimPlan.codeWords.all (fun c => checkMappedNotMMIO mapping
      (MemReloc.imageAddress base (HeapV2ShimPlan.shimOffset + c.1))) = true := by decide +kernel
  exact ⟨atom245 (Wt t) (scopeIs t) _ (by rw [hir]; exact c1) (by decide +kernel) c2 c3⟩

theorem a259 (hir : spec.imageRows = HeapTrapTables.tables.imageRows) :
    CertiFFI.Claim.DeploymentObligation "card:code-static"
      (RtShim.SlotPrem.ShimSlotStatic (Wt t).pins (Wt t).mapping (rowsFootprint spec.imageRows)) := by
  have c : ∀ t : T, HeapStatics.checkSlotStatic (rowsFootprint HeapTrapTables.imageRows) (Wt t).mapping (Wt t).pins = true := by
    decide +kernel
  exact ⟨atom259 spec (Wt t) (by rw [hir]; exact c t)⟩

theorem a262 (hir : spec.imageRows = HeapTrapTables.tables.imageRows) :
    CertiFFI.Claim.DeploymentObligation "card:body-entry/static"
      (HeapV2StepCerts.CodeStatic (Wt t).mapping (Wt t).base (rowsFootprint spec.imageRows).byte) := by
  have c1 : checkImageTableSeparated base mapping HeapV2StepCerts.codeOffsets (rowsFootprint HeapTrapTables.imageRows) = true := by
    decide +kernel
  exact ⟨HeapV2StepCerts.codeStatic_of_checks mapping base _ (by rw [hir]; exact c1) (by decide +kernel) (by decide +kernel)⟩

theorem a263 :
    CertiFFI.Claim.DeploymentObligation "card:body-entry/agrees"
      (ConsumerMapAgrees spec (Wt t).mapping
        (HeapV2E17.consumerMapOn HeapV2E17.noData (Wt t).pins (Wt t).base.toNat (Wt t).mapping (rowsFootprint spec.imageRows).byte)) := by
  refine ⟨HeapV2E17.consumerOn_agrees spec _ _ _ _ ?_⟩
  intro va acc size permitted
  rcases permitted with ⟨_, _, hS, _⟩ | ⟨code, member, hva, _, _⟩
  · exact hS.elim
  · subst hva; exact Normal.mapped_of (List.all_eq_true.1 chk_code_mapped code member)

theorem chk_data_mapped : ∀ t : T, HeapV2Plan.symbolicAccesses.all
    (fun a => Normal.mappedB mapping (HeapV2E17.dataVA (pins t) a)) = true := by decide +kernel

/-- Atom 263 for the data-touching paths (t = 2..5: paths 4, 6, 8, 10): consumer map over all accesses. -/
theorem a263all :
    CertiFFI.Claim.DeploymentObligation "card:body-entry/agrees"
      (ConsumerMapAgrees spec (Wt t).mapping
        (HeapV2E17.consumerMapOn (fun _ => True) (Wt t).pins (Wt t).base.toNat (Wt t).mapping (rowsFootprint spec.imageRows).byte)) := by
  refine ⟨HeapV2E17.consumerOn_agrees spec _ _ _ _ ?_⟩
  intro va acc size permitted
  rcases permitted with ⟨access, member, _, hva, _⟩ | ⟨code, member, hva, _, _⟩
  · subst hva; exact Normal.mapped_of (List.all_eq_true.1 (chk_data_mapped t) access member)
  · subst hva; exact Normal.mapped_of (List.all_eq_true.1 chk_code_mapped code member)

theorem a274 (hir : spec.imageRows = HeapTrapTables.tables.imageRows) :
    CertiFFI.Claim.DeploymentObligation "card:body-entry/tables"
      (∀ (row : NativeSourceInit.PhysicalByte), row ∈ imageRowsPlan spec.imageRows → row ∈ (Wt t).tablePlan) :=
  ⟨fun row h => by rw [hir] at h; exact h⟩

theorem a275 (hir : spec.imageRows = HeapTrapTables.tables.imageRows) :
    CertiFFI.Claim.DeploymentObligation "card:body-entry/declared" (PermissionRowsDeclared (Wt t).rows spec.imageRows) :=
  ⟨show PermissionRowsDeclared HeapTrapTables.permissionRows spec.imageRows from by
    rw [hir]; unfold PermissionRowsDeclared; decide⟩

theorem a276 (hlr : spec.logicalRows = HeapTrapTables.tables.logicalRows) :
    CertiFFI.Claim.DeploymentObligation "E34" (List.map (fun x => x.logical) spec.logicalRows).Nodup :=
  ⟨by rw [hlr]; decide⟩

end spec

end ReleaseProfile.GB10.Heap.TrapInst
#print axioms ReleaseProfile.GB10.Heap.TrapInst.a20
#print axioms ReleaseProfile.GB10.Heap.TrapInst.a123
#print axioms ReleaseProfile.GB10.Heap.TrapInst.a245
#print axioms ReleaseProfile.GB10.Heap.TrapInst.a257
#print axioms ReleaseProfile.GB10.Heap.TrapInst.a259
#print axioms ReleaseProfile.GB10.Heap.TrapInst.a262
#print axioms ReleaseProfile.GB10.Heap.TrapInst.a263
#print axioms ReleaseProfile.GB10.Heap.TrapInst.a264
#print axioms ReleaseProfile.GB10.Heap.TrapInst.a265
#print axioms ReleaseProfile.GB10.Heap.TrapInst.a267
#print axioms ReleaseProfile.GB10.Heap.TrapInst.a270
#print axioms ReleaseProfile.GB10.Heap.TrapInst.a271
#print axioms ReleaseProfile.GB10.Heap.TrapInst.a272
#print axioms ReleaseProfile.GB10.Heap.TrapInst.a273
#print axioms ReleaseProfile.GB10.Heap.TrapInst.a274
#print axioms ReleaseProfile.GB10.Heap.TrapInst.a275
#print axioms ReleaseProfile.GB10.Heap.TrapInst.a276
#print axioms ReleaseProfile.GB10.Heap.TrapInst.a263all
