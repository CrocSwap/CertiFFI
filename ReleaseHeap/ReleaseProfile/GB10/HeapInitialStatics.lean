import ReleaseProfile.GB10.HeapStaticInst
import ArmCertTranslateModel.HeapV2Initial
import Bridge.CruxGenGuarded.ConsumerMapOn

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

/-!
# Heap initial_k (trap) body-entry statics at the clean world

The `card_initial_k` body-entry block (residual indices 262-265, 270-275 of tele-all) at
`W := HeapWorldData.world` with `tableRows := W.tablePlan`. Caller-generic. `satE` is stated for any
`HeapWorld` whose image plan is the world's code ++ shim plan (e.g. a trap-payload world that only
changes the entry data), at its `worldEntry`.
-/

namespace ReleaseProfile.GB10.Heap.InitialStatics

open ReleaseProfile.MachineSource ReleaseProfile.GB10 ReleaseProfile.GB10.Heap ReleaseProfile.GB10.Heap.Statics
open ArmCert.Translate ArmCert.Translate.Model ReleaseProfile.GB10.Heap.StaticInst

/-- Model image plan over `offs` is contained in the world-style plan over `offs ++ t`. -/
theorem mem_imagePlanOf_of {image : MemReloc.Image} {base : MemReloc.Word} {mapping : MemReloc.Mapping}
    {offs t : List Nat} {row : Nat × BitVec 8} (h : row ∈ imagePlan image base mapping offs) :
    row ∈ HeapStatics.imagePlanOf (offs ++ t) image base mapping := by
  simp only [imagePlan, List.mem_filterMap] at h
  obtain ⟨o, ho, hb⟩ := h
  simp only [HeapStatics.imagePlanOf, List.mem_filterMap]
  refine ⟨o, List.mem_append_left _ ho, ?_⟩
  cases hm : mapping (MemReloc.imageAddress base o) <;> cases hi : image o <;> simp_all

def checkPlanAvoidsSlot (plan : NativeSourceInit.Plan) (pins : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) : Bool :=
  match mapping (BitVec.ofNat 64 pins.sp) with
  | none => true
  | some n => plan.all fun r => decide (r.1 < n ∨ n + 16 ≤ r.1)

theorem planAvoidsSlot_of_check {plan : NativeSourceInit.Plan} {pins : HeapV2E17.Pins}
    {mapping : BitVec 64 → Option Nat} (h : checkPlanAvoidsSlot plan pins mapping = true) :
    ∀ row ∈ plan, ¬RtShim2.ShimMem.slotBytes pins mapping row.fst := by
  intro row hr ⟨n, hn, lo, hi⟩
  simp only [checkPlanAvoidsSlot, hn] at h
  have := of_decide_eq_true (List.all_eq_true.1 h row hr)
  omega

/-- satE for any world with the clean world's image-plan shape, at its entry. -/
theorem satE_world (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (w : HeapWorld) (pcount : BitVec 88)
    (himg : w.imagePlan = HeapStatics.imagePlanOf (HeapV2StepCerts.codeOffsets ++ HeapWorldData.shimOffsets)
      (HeapV2.image w.base) w.base w.mapping) :
    NativeSourceInit.Satisfies (HeapV2.entryPlan w.base w.mapping HeapV2StepCerts.codeOffsets w.tablePlan)
      (worldEntry sem rho caller w pcount).mem := by
  intro row hr
  rcases List.mem_append.1 hr with h | h
  · exact world_realizes_image sem rho caller w pcount row (himg ▸ mem_imagePlanOf_of h)
  · exact world_realizes_table sem rho caller w pcount row h

variable (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (pcount : BitVec 88)

section spec

variable {domain : QueryDomain} {spec : TopologyImageSpec domain}

theorem a262 (hir : spec.imageRows = HeapWorldTables.tables.imageRows) :
    CertiFFI.Claim.DeploymentObligation "card:body-entry/static"
      (HeapV2StepCerts.CodeStatic W.mapping W.base (rowsFootprint spec.imageRows).byte) :=
  ⟨HeapV2StepCerts.codeStatic_of_checks W.mapping W.base _ (by rw [hir]; decide +kernel) (by decide +kernel)
    (by decide +kernel)⟩

theorem a263 :
    CertiFFI.Claim.DeploymentObligation "card:body-entry/agrees"
      (ConsumerMapAgrees spec W.mapping
        (HeapV2E17.consumerMapOn HeapV2E17.noData W.pins W.base.toNat W.mapping (rowsFootprint spec.imageRows).byte)) := by
  refine ⟨HeapV2E17.consumerOn_agrees spec _ _ _ _ ?_⟩
  intro va acc size permitted
  rcases permitted with ⟨_, _, hS, _⟩ | ⟨code, member, hva, _, _⟩
  · exact hS.elim
  · subst hva; exact Normal.mapped_of (List.all_eq_true.1 Normal.world_code_mapped code member)

theorem a274 (hir : spec.imageRows = HeapWorldTables.tables.imageRows) :
    CertiFFI.Claim.DeploymentObligation "card:body-entry/tables"
      (∀ (row : NativeSourceInit.PhysicalByte), row ∈ imageRowsPlan spec.imageRows → row ∈ W.tablePlan) :=
  ⟨fun row h => by rw [hir] at h; exact h⟩

theorem a275 (hir : spec.imageRows = HeapWorldTables.tables.imageRows) :
    CertiFFI.Claim.DeploymentObligation "card:body-entry/declared" (PermissionRowsDeclared W.rows spec.imageRows) :=
  ⟨by rw [hir]; unfold PermissionRowsDeclared; decide⟩

end spec

theorem a264 : CertiFFI.Claim.DeploymentObligation "card:body-entry/page" (W.base.toNat % 4096 = 0) := ⟨by decide⟩

theorem a265 : CertiFFI.Claim.DeploymentObligation "card:body-entry/low" (W.base.toNat < 2 ^ 54) := ⟨by decide⟩

set_option maxRecDepth 200000 in
theorem a270 : CertiFFI.Claim.DeploymentObligation "card:body-entry/satE"
    (NativeSourceInit.Satisfies (HeapV2.entryPlan W.base W.mapping HeapV2StepCerts.codeOffsets W.tablePlan)
      (E rho caller pcount).mem) :=
  ⟨satE_world worldSemantics rho caller W pcount rfl⟩

theorem a271 : CertiFFI.Claim.DeploymentObligation "card:body-entry/planAvoidsSlot"
    (∀ (row : NativeSourceInit.PhysicalByte),
      row ∈ HeapV2.entryPlan W.base W.mapping HeapV2StepCerts.codeOffsets W.tablePlan →
        ¬RtShim2.ShimMem.slotBytes W.pins W.mapping row.fst) :=
  ⟨planAvoidsSlot_of_check (by decide +kernel)⟩

theorem a272 : CertiFFI.Claim.DeploymentObligation "card:body-entry/codeMapped"
    (∀ (o : Nat), o ∈ HeapV2StepCerts.codeOffsets → ∃ pa, W.mapping (MemReloc.imageAddress W.base o) = some pa) := by
  refine ⟨fun o ho => Option.isSome_iff_exists.1 ?_⟩
  have h : HeapV2StepCerts.codeOffsets.all (fun o => (W.mapping (MemReloc.imageAddress W.base o)).isSome) = true := by
    decide +kernel
  exact List.all_eq_true.1 h o ho

theorem a273 : CertiFFI.Claim.DeploymentObligation "card:body-entry/codePresent"
    (∀ (o : Nat), o ∈ HeapV2StepCerts.codeOffsets → ∃ byte, HeapV2.image W.base o = some byte) := by
  refine ⟨fun o ho => Option.isSome_iff_exists.1 ?_⟩
  have h : HeapV2StepCerts.codeOffsets.all (fun o => (HeapV2.image W.base o).isSome) = true := by decide +kernel
  exact List.all_eq_true.1 h o ho

end ReleaseProfile.GB10.Heap.InitialStatics
#print axioms ReleaseProfile.GB10.Heap.InitialStatics.a262
#print axioms ReleaseProfile.GB10.Heap.InitialStatics.a263
#print axioms ReleaseProfile.GB10.Heap.InitialStatics.a264
#print axioms ReleaseProfile.GB10.Heap.InitialStatics.a265
#print axioms ReleaseProfile.GB10.Heap.InitialStatics.a270
#print axioms ReleaseProfile.GB10.Heap.InitialStatics.a271
#print axioms ReleaseProfile.GB10.Heap.InitialStatics.a272
#print axioms ReleaseProfile.GB10.Heap.InitialStatics.a273
#print axioms ReleaseProfile.GB10.Heap.InitialStatics.a274
#print axioms ReleaseProfile.GB10.Heap.InitialStatics.a275
