import ReleaseProfile.GB10.HeapClosedB
import ReleaseProfile.GB10.HeapInitialStatics

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 200000

/-!
# Heap statics at data variants of the clean world

`WD d:= { HeapWorldData.world with data:= d }` for any entry data `d` (e.g.
`variantWorld x2 x3`, gpr x2/x3 changed). Entry-independent atoms are the clean-world ones (defeq);
entry-dependent atoms (closed, placed, slot/data present, satE) are proved at `worldEntry … (WD d)`.
The closed atom needs `d`'s page-table roots to be the world's (TTBR0 = HTTBR = 0x80000000, TTBR1 = 0).
Field names follow `Heap.Trap.TrapStaticsAt`.
-/

namespace ReleaseProfile.GB10.Heap.VariantStatics

open ReleaseProfile.MachineSource ReleaseProfile.GB10 ReleaseProfile.GB10.Heap ReleaseProfile.GB10.Heap.Statics
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ReleaseProfile.GB10.HeapClosedB

abbrev WD (d : DataPart) : HeapWorld := { HeapWorldData.world with data := d }

abbrev ED (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (d : DataPart) (pcount : BitVec 88) :=
  worldEntry worldSemantics rho caller (WD d) pcount

theorem imagePlan_eq : HeapWorldData.imagePlan =
    HeapStatics.imagePlanOf (HeapV2StepCerts.codeOffsets ++ HeapWorldData.shimOffsets)
      (HeapV2.image HeapWorldData.base) HeapWorldData.base HeapWorldData.mapping := by
  unfold HeapWorldData.imagePlan; rfl

/-- The world-entry register reads for any world whose data carries the clean page-table roots. -/
theorem worldRegs_of_data (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (w : HeapWorld) (pcount : BitVec 88) (h0 : w.data.TTBR0_EL2 = 0x80000000#128) (h1 : w.data.TTBR1_EL2 = 0#128)
    (hh : w.data.HTTBR = 0x80000000#64) :
    WorldRegs (worldEntry sem rho caller w pcount).regs
      (controlWord rho.val caller.caller .TCR_EL2) (controlWord rho.val caller.caller .SCTLR_EL2) := by
  have hd : (worldEntry sem rho caller w pcount).regs = sourceRegs rho caller { w.data with PhysicalCount := pcount } := rfl
  rw [hd]
  refine ⟨h0, h1, (show sourceBank64 rho caller { w.data with PhysicalCount := pcount } .HTTBR = _ from by
      unfold sourceBank64; simp only [↓reduceDIte]; exact hh),
    sourceRegs_bank64 rho caller _ .TCR_EL2, sourceRegs_bank64 rho caller _ .SCTLR_EL2,
    sourceRegs_feature rho caller _ 227 (by decide) false _ rfl,
    sourceRegs_feature rho caller _ 81 (by decide) true _ rfl,
    sourceRegs_feature rho caller _ 101 (by decide) true _ rfl, rfl, ?_, ?_, ?_⟩
  · bit1 .TCR_EL2 7 false
  · bit1 .SCTLR_EL2 12 true
  · bit1 .SCTLR_EL2 2 true

variable (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (d : DataPart) (pcount : BitVec 88)

theorem a20 : CertiFFI.Claim.DeploymentObligation "comp:caller:image-table-separated"
    (ImageTableSeparated (WD d).scope (WD d).loadBase (WD d).mapping (RtShim2.ShimMem.slotBytes (WD d).pins (WD d).mapping)) :=
  StaticInst.a20

theorem a123 : CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/placed"
    (MemReloc.ImageOn (WD d).scope (WD d).image (ED rho caller d pcount) (WD d).loadBase (WD d).mapping) :=
  ⟨imageOn_mono (fun _ h => h.elim (fun h => List.mem_append.2 (Or.inr h)) (fun h => List.mem_append.2 (Or.inl h)))
    (HeapStatics.imageOn_of_imagePlan
      (fun a b m => world_realizes_image worldSemantics rho caller (WD d) pcount (a, b)
        (show (a, b) ∈ HeapWorldData.imagePlan from imagePlan_eq ▸ m))
      (show HeapStatics.checkImageDefined (HeapV2StepCerts.codeOffsets ++ HeapWorldData.shimOffsets)
        (HeapV2.image HeapWorldData.base) HeapWorldData.base HeapWorldData.mapping = true from by decide +kernel))⟩

theorem a256 : CertiFFI.Claim.DeploymentObligation "card:slot-present"
    (RtShim.SlotPrem.ShimSlotPresent (WD d).pins (WD d).mapping (ED rho caller d pcount)) :=
  ⟨atom257 worldSemantics rho caller (WD d) pcount
    (show HeapStatics.checkSlotPresent HeapWorldData.pins HeapWorldData.mapping HeapWorldData.slotPlan = true from by
      decide +kernel)⟩

theorem a266 : CertiFFI.Claim.DeploymentObligation "card:body-entry/presentE"
    (HeapV2StepCerts.C3.DataPresent (WD d).pins (WD d).mapping (ED rho caller d pcount)) :=
  ⟨atom264 worldSemantics rho caller (WD d) pcount
    (show HeapStatics.checkDataPresent HeapWorldData.pins HeapWorldData.mapping HeapWorldData.dataPlan = true from by
      decide +kernel)⟩

theorem a269 : CertiFFI.Claim.DeploymentObligation "card:body-entry/satE"
    (NativeSourceInit.Satisfies (HeapV2.entryPlan (WD d).base (WD d).mapping HeapV2StepCerts.codeOffsets
      (imageRowsPlan HeapWorldTables.imageRows)) (ED rho caller d pcount).mem) :=
  ⟨InitialStatics.satE_world worldSemantics rho caller (WD d) pcount imagePlan_eq⟩

theorem a270 : CertiFFI.Claim.DeploymentObligation "card:body-entry/planAvoidsSlot"
    (∀ (row : NativeSourceInit.PhysicalByte),
      row ∈ HeapV2.entryPlan (WD d).base (WD d).mapping HeapV2StepCerts.codeOffsets (imageRowsPlan HeapWorldTables.imageRows) →
        ¬RtShim2.ShimMem.slotBytes (WD d).pins (WD d).mapping row.fst) :=
  InitialStatics.a271

section spec

variable {domain : QueryDomain} {spec : TopologyImageSpec domain}

theorem a244 (hir : spec.imageRows = HeapWorldTables.tables.imageRows) :
    CertiFFI.Claim.DeploymentObligation "card:code-static"
      (RtDit.ShimFetch.ShimCodeStatic (WD d).mapping (WD d).base (WD d).scope (rowsFootprint spec.imageRows).byte) :=
  StaticInst.a244 hir

theorem a258 (hir : spec.imageRows = HeapWorldTables.tables.imageRows) :
    CertiFFI.Claim.DeploymentObligation "card:code-static"
      (RtShim.SlotPrem.ShimSlotStatic (WD d).pins (WD d).mapping (rowsFootprint spec.imageRows)) :=
  StaticInst.a258 hir

theorem a261 (hir : spec.imageRows = HeapWorldTables.tables.imageRows) :
    CertiFFI.Claim.DeploymentObligation "card:body-entry/static"
      (HeapV2StepCerts.CodeStatic (WD d).mapping (WD d).base (rowsFootprint spec.imageRows).byte) :=
  InitialStatics.a262 hir

theorem a262 :
    CertiFFI.Claim.DeploymentObligation "card:body-entry/agrees"
      (ConsumerMapAgrees spec (WD d).mapping
        (HeapV2E17.consumerMapOn (fun _ => True) (WD d).pins (WD d).base.toNat (WD d).mapping (rowsFootprint spec.imageRows).byte)) := by
  refine ⟨HeapV2E17.consumerOn_agrees spec _ _ _ _ ?_⟩
  intro va acc size permitted
  rcases permitted with ⟨access, member, _, hva, _⟩ | ⟨code, member, hva, _, _⟩
  · subst hva; exact Normal.mapped_of (List.all_eq_true.1 Normal.world_data_mapped access member)
  · subst hva; exact Normal.mapped_of (List.all_eq_true.1 Normal.world_code_mapped code member)

theorem a274 (hir : spec.imageRows = HeapWorldTables.tables.imageRows) :
    CertiFFI.Claim.DeploymentObligation "card:body-entry/declared" (PermissionRowsDeclared (WD d).rows spec.imageRows) :=
  InitialStatics.a275 hir

end spec

section closed

variable {specCaller : AdmissibleCaller rho}
  {spec : TopologyImageSpec (fun q => ∃ q0 ∈ HeapWorldTables.queries, SamePage q0.va q.va)}

theorem a122 (h0 : d.TTBR0_EL2 = 0x80000000#128) (h1 : d.TTBR1_EL2 = 0#128) (hh : d.HTTBR = 0x80000000#64)
    (sspec : SourceSpec rho specCaller spec) (hlay : spec.layout = HeapWorldTables.tables.layout)
    (hlr : spec.logicalRows = HeapWorldTables.tables.logicalRows)
    (hir : spec.imageRows = HeapWorldTables.tables.imageRows) :
    CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/closed"
      (ClosedMembershipAt spec (sourceAttributes rho caller) (WD d).rows (WD d).mapping
        (ArmBridge.CruxGenGuarded.Release.shimMap spec (WD d).mapping (WD d).base (WD d).pins)
        (ArmBridge.CruxGenGuarded.beforeFetchState (ED rho caller d pcount))) :=
  ⟨closed_at_regs (worldSpec_tables rho sspec hlay hlr hir) (fun _ h => h) _
    (worldRegs_before (worldRegs_of_data worldSemantics rho caller (WD d) pcount h0 h1 hh))⟩

end closed

end ReleaseProfile.GB10.Heap.VariantStatics
#print axioms ReleaseProfile.GB10.Heap.VariantStatics.a20
#print axioms ReleaseProfile.GB10.Heap.VariantStatics.a122
#print axioms ReleaseProfile.GB10.Heap.VariantStatics.a123
#print axioms ReleaseProfile.GB10.Heap.VariantStatics.a244
#print axioms ReleaseProfile.GB10.Heap.VariantStatics.a256
#print axioms ReleaseProfile.GB10.Heap.VariantStatics.a258
#print axioms ReleaseProfile.GB10.Heap.VariantStatics.a261
#print axioms ReleaseProfile.GB10.Heap.VariantStatics.a262
#print axioms ReleaseProfile.GB10.Heap.VariantStatics.a266
#print axioms ReleaseProfile.GB10.Heap.VariantStatics.a269
#print axioms ReleaseProfile.GB10.Heap.VariantStatics.a270
#print axioms ReleaseProfile.GB10.Heap.VariantStatics.a274
