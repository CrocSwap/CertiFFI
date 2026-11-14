import ReleaseProfile.GB10.HeapC2Normal

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

/-!
# Heap world variants for the path-selector families (initial_k / ct_k)

`variantWorld x2 x3` is the clean Heap world with only the entry's x2/x3 changed (what `qOf` reads, i.e.
which path the card selects). Program, memory, tables and every other entry register are the world's.
The entry-dependent normal atoms are restated at the variant entry; the program-only atoms
(Normal.a16..a19, a245, a246, a259, a261, a271, a274, budget_small) apply unchanged by definitional equality.
-/

namespace ReleaseProfile.GB10.Heap.Variant

open ReleaseProfile.MachineSource ReleaseProfile.GB10 ReleaseProfile.GB10.Heap ReleaseProfile.GB10.Heap.Normal

#check "CURRENT_DECL GB10.Heap.Variant.variantWorld"
def variantWorld (x2 x3 : BitVec 64) : HeapWorld :=
  { W with data := { HeapWorldData.data with gpr := (HeapWorldData.data.gpr.set 2 x2).set 3 x3 } }

variable (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (x2 x3 : BitVec 64) (pcount : BitVec 88)

abbrev V := variantWorld x2 x3

abbrev EV := worldEntry worldSemantics rho caller (V x2 x3) pcount

theorem gpr_ne (i : Nat) (h : i < 31) (h2 : i ≠ 2) (h3 : i ≠ 3) :
    (EV rho caller x2 x3 pcount).regs.gpr[i] = HeapWorldData.data.gpr[i] := by
  show ((HeapWorldData.data.gpr.set 2 x2).set 3 x3)[i] = _
  rw [Vector.getElem_set_ne _ _ (by omega), Vector.getElem_set_ne _ _ (by omega)]

theorem a121 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pc"
    ((EV rho caller x2 x3 pcount).regs._PC = (V x2 x3).base + (V x2 x3).offS 0) := by
  refine ⟨?_⟩
  show HeapWorldData.data._PC = HeapWorldData.base + HeapV2Card.Instance.offS 0
  rw [HeapV2Card.Instance.rc_offPre 0 (by decide)]
  decide

theorem a257 : CertiFFI.Claim.CallerContract "comp:caller:shim-caller-contract"
    ((EV rho caller x2 x3 pcount).regs.SP_EL0 = BitVec.ofNat 64 (V x2 x3).pins.sp + BitVec.ofInt 64 16) := by
  refine ⟨?_⟩
  show HeapWorldData.data.SP_EL0 = BitVec.ofNat 64 HeapWorldData.pins.sp + BitVec.ofInt 64 16
  decide

theorem a264 : CertiFFI.Claim.CallerContract "comp:caller:caller-buffers"
    (HeapV2StepCerts.RegBind.regVal (EV rho caller x2 x3 pcount) (HeapV2StepCerts.RegBind.Reg.x 0) =
      BitVec.ofInt 64 ↑(V x2 x3).pins.x0) := by
  refine ⟨?_⟩
  simp only [HeapV2StepCerts.RegBind.regVal]
  show ((HeapWorldData.data.gpr.set 2 x2).set 3 x3)[((0 : Fin 31) : Nat)] = BitVec.ofInt 64 ↑HeapWorldData.pins.x0
  rw [Vector.getElem_set_ne _ _ (by decide), Vector.getElem_set_ne _ _ (by decide)]
  decide

theorem a265 : CertiFFI.Claim.CallerContract "comp:caller:caller-buffers"
    (HeapV2StepCerts.RegBind.regVal (EV rho caller x2 x3 pcount) (HeapV2StepCerts.RegBind.Reg.x 1) =
      BitVec.ofInt 64 ↑(V x2 x3).pins.x1) := by
  refine ⟨?_⟩
  simp only [HeapV2StepCerts.RegBind.regVal]
  show ((HeapWorldData.data.gpr.set 2 x2).set 3 x3)[((1 : Fin 31) : Nat)] = BitVec.ofInt 64 ↑HeapWorldData.pins.x1
  rw [Vector.getElem_set_ne _ _ (by decide), Vector.getElem_set_ne _ _ (by decide)]
  decide

theorem a269 : CertiFFI.Claim.CallerContract "card:default-caller-return-low"
    ((EV rho caller x2 x3 pcount).regs.gpr[30].toNat < 2 ^ 55) := by
  refine ⟨?_⟩
  rw [gpr_ne rho caller x2 x3 pcount 30 (by decide) (by decide) (by decide)]
  show HeapWorldData.data.gpr[30].toNat < 2 ^ 55
  decide

theorem a270 : CertiFFI.Claim.CallerContract "card:default-caller-return-target"
    ((EV rho caller x2 x3 pcount).regs.gpr[30] = (V x2 x3).base + (V x2 x3).offS 369) := by
  refine ⟨?_⟩
  rw [gpr_ne rho caller x2 x3 pcount 30 (by decide) (by decide) (by decide)]
  show HeapWorldData.data.gpr[30] = HeapWorldData.base + HeapV2Card.Instance.offS 369
  decide

theorem a243 : CertiFFI.Claim.DeploymentObligation "card:default369-initial-tag-status-rows"
    (NativeMteTagCheck.TagStatusRows (EV rho caller x2 x3 pcount) ((EV rho caller x2 x3 pcount).choiceOcc.getD 1354 0) 112) :=
  ⟨world_tagStatusRows rho caller (V x2 x3) pcount 112⟩

/-- The variant entry's register file differs from the world entry's only in data gpr; every walk/image
fact used by `world_images`/`a211` is about features, control words and memory, all equal. -/
theorem images {domain : ArmCert.Translate.Model.QueryDomain} {spec : ArmCert.Translate.Model.TopologyImageSpec domain}
    {specCaller : AdmissibleCaller rho} (sspec : SourceSpec rho specCaller spec)
    (hir : spec.imageRows = HeapWorldTables.tables.imageRows) :
    ArmCert.Translate.Model.CurrentImagesAt spec (sourceAttributes rho caller) W.rows
        (ArmBridge.CruxGenGuarded.beforeFetchState (EV rho caller x2 x3 pcount)) ∧
      ArmCertWalk.RawImageAt spec.imageRows (ArmBridge.CruxGenGuarded.beforeFetchState (EV rho caller x2 x3 pcount)).mem := by
  obtain ⟨ha, hd, pie, -, -, -, -, -, -, cpie, -⟩ := sourceSpec_walkLiterals rho specCaller sspec (worldPayload W pcount).data
  have wxn := wxn_lit rho specCaller sspec (worldPayload W pcount).data
  have cha := controls_ha_lit rho specCaller sspec (worldPayload W pcount).data
  have chd := controls_hd_lit rho specCaller sspec (worldPayload W pcount).data
  have cov := (sspec.overlay (worldPayload W pcount).data).trans (overlay_source rho specCaller _)
  have nv1 := nv1Mode_el20 spec.controls sspec.regime
  have off : ArmCertWalk.e0OverlayEnabled
      (ArmBridge.CruxGenGuarded.beforeFetchState (EV rho caller x2 x3 pcount)).regs = false := by
    rw [beforeFetch_regs]
    exact e0Overlay_source rho caller (worldPayload (V x2 x3) pcount).data
  have sat : NativeSourceInit.Satisfies W.tablePlan
      (ArmBridge.CruxGenGuarded.beforeFetchState (EV rho caller x2 x3 pcount)).mem :=
    world_realizes_table worldSemantics rho caller (V x2 x3) pcount
  refine images_of_checks spec (sourceAttributes rho caller) W.rows
    (ArmBridge.CruxGenGuarded.beforeFetchState (EV rho caller x2 x3 pcount)) (plan := W.tablePlan)
    sat ?_ ?_ ?_ ?_ ?_ ?_ (ArmBridge.CruxGenGuarded.beforeFetchState (EV rho caller x2 x3 pcount)).regs off off ?_
  · intro x hx
    rw [hir] at hx
    exact hx
  · rw [hir]; unfold ArmCert.Translate.Model.PermissionRowsDeclared; decide
  · rw [hir]; decide
  · rw [hir, pie, ha, hd]; decide
  · rw [hir]; exact checkAttr_world rho caller
  · rw [hir]; exact checkWB_world rho caller
  · rw [checkPermissionImagePure_noOverlay _ _ _ _ off]
    simp only [checkPermissionImageNoOverlay, permissionParamsView, ha, hd, pie, wxn,
      ArmCertWalk.descriptorPermissionView, S1LogicalReference.leafPermissions,
      S1LogicalReference.classicPermissions, nv1, cpie, cha, chd, cov, Bool.false_eq_true, ↓reduceIte]
    decide

theorem a211 {domain : ArmCert.Translate.Model.QueryDomain} {spec : ArmCert.Translate.Model.TopologyImageSpec domain}
    {specCaller : AdmissibleCaller rho} (sspec : SourceSpec rho specCaller spec)
    (hir : spec.imageRows = HeapWorldTables.tables.imageRows) :
    CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/noUpd" (∀ (wr : Bool) (acc : ArmFull.AccessDescriptor), ArmCert.Translate.Model.DataShape wr acc → ArmCertWalk.NoUpdateRows (have __src := spec.params; { ha := __src.ha, hd := __src.hd, tbi := __src.tbi, tbid := __src.tbid, nfd := __src.nfd, e0pd := __src.e0pd, d128 := __src.d128, aie := __src.aie, mair2 := __src.mair2, ds := __src.ds, ps := __src.ps, txsz := __src.txsz, epan := __src.epan, dct := __src.dct, nv1 := __src.nv1, cmow := __src.cmow, pnch := __src.pnch, disch := __src.disch, haft := ArmCert.Translate.Model.hostHAFT (EV rho caller x2 x3 pcount).regs, mtx := __src.mtx, skl := __src.skl, pie := __src.pie, pir := __src.pir, pire0 := __src.pire0, emec := __src.emec, amec := __src.amec, t0sz := __src.t0sz, t1sz := __src.t1sz, uwxn := __src.uwxn, tgx := __src.tgx, irgn := __src.irgn, orgn := __src.orgn, sh := __src.sh, hpd := __src.hpd, ee := __src.ee, wxn := __src.wxn, ntlsmd := __src.ntlsmd, dc := __src.dc, sif := __src.sif, mair := __src.mair }) acc spec.imageRows = true) := by
  obtain ⟨ha, hd, pie, -⟩ := sourceSpec_walkLiterals rho specCaller sspec (worldPayload W pcount).data
  have f189 := sourceRegs_feature rho caller (worldPayload (V x2 x3) pcount).data 189 (by decide) false _ rfl
  refine ⟨noUpd_of_view _ _ (fun w => ?_)⟩
  simp only [noUpdateParamsView, ha, hd, pie]
  have haft : ArmCert.Translate.Model.hostHAFT (EV rho caller x2 x3 pcount).regs = 0#1 := by
    unfold ArmCert.Translate.Model.hostHAFT
    show (if (sourceRegs rho caller (worldPayload (V x2 x3) pcount).data).FeatureImpl[189] && _ && _ then _ else _) = _
    rw [f189]
    rfl
  rw [haft, hir]
  cases w <;> decide

/-! ## World-generic image and no-update atoms (any world with the clean world's tables and rows) -/

section generic

variable (w : HeapWorld)

#check "CURRENT_DECL GB10.Heap.Variant.images_w"
theorem images_w (htab : w.tablePlan = W.tablePlan) (hrows : w.rows = W.rows)
    {domain : ArmCert.Translate.Model.QueryDomain} {spec : ArmCert.Translate.Model.TopologyImageSpec domain}
    {specCaller : AdmissibleCaller rho} (sspec : SourceSpec rho specCaller spec)
    (hir : spec.imageRows = HeapWorldTables.tables.imageRows) :
    ArmCert.Translate.Model.CurrentImagesAt spec (sourceAttributes rho caller) w.rows
        (ArmBridge.CruxGenGuarded.beforeFetchState (worldEntry worldSemantics rho caller w pcount)) ∧
      ArmCertWalk.RawImageAt spec.imageRows
        (ArmBridge.CruxGenGuarded.beforeFetchState (worldEntry worldSemantics rho caller w pcount)).mem := by
  rw [hrows]
  obtain ⟨ha, hd, pie, -, -, -, -, -, -, cpie, -⟩ := sourceSpec_walkLiterals rho specCaller sspec (worldPayload W pcount).data
  have wxn := wxn_lit rho specCaller sspec (worldPayload W pcount).data
  have cha := controls_ha_lit rho specCaller sspec (worldPayload W pcount).data
  have chd := controls_hd_lit rho specCaller sspec (worldPayload W pcount).data
  have cov := (sspec.overlay (worldPayload W pcount).data).trans (overlay_source rho specCaller _)
  have nv1 := nv1Mode_el20 spec.controls sspec.regime
  have off : ArmCertWalk.e0OverlayEnabled
      (ArmBridge.CruxGenGuarded.beforeFetchState (worldEntry worldSemantics rho caller w pcount)).regs = false := by
    rw [beforeFetch_regs]
    exact e0Overlay_source rho caller (worldPayload w pcount).data
  have sat : NativeSourceInit.Satisfies W.tablePlan
      (ArmBridge.CruxGenGuarded.beforeFetchState (worldEntry worldSemantics rho caller w pcount)).mem :=
    htab ▸ world_realizes_table worldSemantics rho caller w pcount
  refine images_of_checks spec (sourceAttributes rho caller) W.rows
    (ArmBridge.CruxGenGuarded.beforeFetchState (worldEntry worldSemantics rho caller w pcount)) (plan := W.tablePlan)
    sat ?_ ?_ ?_ ?_ ?_ ?_ (ArmBridge.CruxGenGuarded.beforeFetchState (worldEntry worldSemantics rho caller w pcount)).regs
    off off ?_
  · intro x hx
    rw [hir] at hx
    exact hx
  · rw [hir]; unfold ArmCert.Translate.Model.PermissionRowsDeclared; decide
  · rw [hir]; decide
  · rw [hir, pie, ha, hd]; decide
  · rw [hir]; exact checkAttr_world rho caller
  · rw [hir]; exact checkWB_world rho caller
  · rw [checkPermissionImagePure_noOverlay _ _ _ _ off]
    simp only [checkPermissionImageNoOverlay, permissionParamsView, ha, hd, pie, wxn,
      ArmCertWalk.descriptorPermissionView, S1LogicalReference.leafPermissions,
      S1LogicalReference.classicPermissions, nv1, cpie, cha, chd, cov, Bool.false_eq_true, ↓reduceIte]
    decide

#check "CURRENT_DECL GB10.Heap.Variant.a211_w"
theorem a211_w {domain : ArmCert.Translate.Model.QueryDomain} {spec : ArmCert.Translate.Model.TopologyImageSpec domain}
    {specCaller : AdmissibleCaller rho} (sspec : SourceSpec rho specCaller spec)
    (hir : spec.imageRows = HeapWorldTables.tables.imageRows) :
    CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/noUpd" (∀ (wr : Bool) (acc : ArmFull.AccessDescriptor), ArmCert.Translate.Model.DataShape wr acc → ArmCertWalk.NoUpdateRows (have __src := spec.params; { ha := __src.ha, hd := __src.hd, tbi := __src.tbi, tbid := __src.tbid, nfd := __src.nfd, e0pd := __src.e0pd, d128 := __src.d128, aie := __src.aie, mair2 := __src.mair2, ds := __src.ds, ps := __src.ps, txsz := __src.txsz, epan := __src.epan, dct := __src.dct, nv1 := __src.nv1, cmow := __src.cmow, pnch := __src.pnch, disch := __src.disch, haft := ArmCert.Translate.Model.hostHAFT (worldEntry worldSemantics rho caller w pcount).regs, mtx := __src.mtx, skl := __src.skl, pie := __src.pie, pir := __src.pir, pire0 := __src.pire0, emec := __src.emec, amec := __src.amec, t0sz := __src.t0sz, t1sz := __src.t1sz, uwxn := __src.uwxn, tgx := __src.tgx, irgn := __src.irgn, orgn := __src.orgn, sh := __src.sh, hpd := __src.hpd, ee := __src.ee, wxn := __src.wxn, ntlsmd := __src.ntlsmd, dc := __src.dc, sif := __src.sif, mair := __src.mair }) acc spec.imageRows = true) := by
  obtain ⟨ha, hd, pie, -⟩ := sourceSpec_walkLiterals rho specCaller sspec (worldPayload W pcount).data
  have f189 := sourceRegs_feature rho caller (worldPayload w pcount).data 189 (by decide) false _ rfl
  refine ⟨noUpd_of_view _ _ (fun wr => ?_)⟩
  simp only [noUpdateParamsView, ha, hd, pie]
  have haft : ArmCert.Translate.Model.hostHAFT (worldEntry worldSemantics rho caller w pcount).regs = 0#1 := by
    unfold ArmCert.Translate.Model.hostHAFT
    show (if (sourceRegs rho caller (worldPayload w pcount).data).FeatureImpl[189] && _ && _ then _ else _) = _
    rw [f189]
    rfl
  rw [haft, hir]
  cases wr <;> decide

end generic

/-! ## Table-generic image atoms (any tables/rows; per-table checks as finite Bool hypotheses) -/

section tableGeneric

/-- The walk parameters the image checks read, at their source values. -/
def imageParamsLit : ArmFull.S1TTWParams :=
  { (default : ArmFull.S1TTWParams) with ha := 1#1, hd := 1#1, pie := 0#1, wxn := 0#1 }

variable (w : HeapWorld) {domain : ArmCert.Translate.Model.QueryDomain}

#check "CURRENT_DECL GB10.Heap.Variant.images_tw"
theorem images_tw (t : TopologyTables domain) (htab : w.tablePlan = ArmCert.Translate.Model.imageRowsPlan t.imageRows)
    (hdecl : ArmCert.Translate.Model.PermissionRowsDeclared w.rows t.imageRows)
    (hcov : ArmCert.Translate.Model.checkPermissionRowsCovered w.rows (ArmCert.Translate.Model.rowsFootprint t.imageRows) = true)
    (hpure : ArmCert.Translate.Model.checkImagePure t.imageRows (0#1 == 1#1) (1#1 == 1#1) (1#1 == 1#1) = true)
    (hattr : ∀ b : Bool, t.imageRows.all (fun row => !row.leaf || decide (ArmCertWalk.reservedAttribute true b
      (ArmCertWalk.mairByte 0x000000040044ffff#64 (ArmCertWalk.descriptorIndex row.raw)) = false)) = true)
    (hwb : t.imageRows.all (fun row => !row.leaf || ArmCert.Translate.Model.writeBackByte
      (ArmCertWalk.mairByte 0x000000040044ffff#64 (ArmCertWalk.descriptorIndex row.raw))) = true)
    (hperm : ∀ c : S1LogicalReference.Controls, c.pie = false → (c.poe || c.e0poe) = false →
      S1LogicalReference.nv1Mode c = false → c.ha = true → c.hd = true →
      checkPermissionImageNoOverlay w.rows (permissionParamsView imageParamsLit) c = true)
    {spec : ArmCert.Translate.Model.TopologyImageSpec domain}
    {specCaller : AdmissibleCaller rho} (sspec : SourceSpec rho specCaller spec)
    (hir : spec.imageRows = t.imageRows) :
    ArmCert.Translate.Model.CurrentImagesAt spec (sourceAttributes rho caller) w.rows
        (ArmBridge.CruxGenGuarded.beforeFetchState (worldEntry worldSemantics rho caller w pcount)) ∧
      ArmCertWalk.RawImageAt spec.imageRows
        (ArmBridge.CruxGenGuarded.beforeFetchState (worldEntry worldSemantics rho caller w pcount)).mem := by
  obtain ⟨ha, hd, pie, -, -, -, -, -, -, cpie, -⟩ := sourceSpec_walkLiterals rho specCaller sspec (worldPayload W pcount).data
  have wxn := wxn_lit rho specCaller sspec (worldPayload W pcount).data
  have cha := controls_ha_lit rho specCaller sspec (worldPayload W pcount).data
  have chd := controls_hd_lit rho specCaller sspec (worldPayload W pcount).data
  have cov := (sspec.overlay (worldPayload W pcount).data).trans (overlay_source rho specCaller _)
  have nv1 := nv1Mode_el20 spec.controls sspec.regime
  have off : ArmCertWalk.e0OverlayEnabled
      (ArmBridge.CruxGenGuarded.beforeFetchState (worldEntry worldSemantics rho caller w pcount)).regs = false := by
    rw [beforeFetch_regs]
    exact e0Overlay_source rho caller (worldPayload w pcount).data
  have sat : NativeSourceInit.Satisfies (ArmCert.Translate.Model.imageRowsPlan t.imageRows)
      (ArmBridge.CruxGenGuarded.beforeFetchState (worldEntry worldSemantics rho caller w pcount)).mem :=
    htab ▸ world_realizes_table worldSemantics rho caller w pcount
  have pview : permissionParamsView spec.params = permissionParamsView imageParamsLit := by
    simp only [permissionParamsView, imageParamsLit, ha, hd, pie, wxn]
  refine images_of_checks spec (sourceAttributes rho caller) w.rows
    (ArmBridge.CruxGenGuarded.beforeFetchState (worldEntry worldSemantics rho caller w pcount))
    (plan := ArmCert.Translate.Model.imageRowsPlan t.imageRows)
    sat ?_ ?_ ?_ ?_ ?_ ?_ (ArmBridge.CruxGenGuarded.beforeFetchState (worldEntry worldSemantics rho caller w pcount)).regs
    off off ?_
  · intro x hx
    rw [hir] at hx
    exact hx
  · rw [hir]; exact hdecl
  · rw [hir]; exact hcov
  · rw [hir, pie, ha, hd]; exact hpure
  · rw [hir]
    have h : ArmCert.Translate.Model.checkAttributeImage t.imageRows (sourceAttributes rho caller) =
        t.imageRows.all (fun row => !row.leaf || decide (ArmCertWalk.reservedAttribute
          (sourceAttributes rho caller).xs (sourceAttributes rho caller).mte2
          (ArmCertWalk.mairByte (sourceAttributes rho caller).mair (ArmCertWalk.descriptorIndex row.raw)) = false)) :=
      rfl
    rw [h, sourceAttributes_mair rho caller, sourceAttributes_xs rho caller]
    exact hattr _
  · rw [hir]
    have h : ArmCert.Translate.Model.checkWriteBackAttributeImage t.imageRows (sourceAttributes rho caller) =
        t.imageRows.all (fun row => !row.leaf || ArmCert.Translate.Model.writeBackByte
          (ArmCertWalk.mairByte (sourceAttributes rho caller).mair (ArmCertWalk.descriptorIndex row.raw))) :=
      rfl
    rw [h, sourceAttributes_mair rho caller]
    exact hwb
  · rw [checkPermissionImagePure_noOverlay _ _ _ _ off, pview]
    exact hperm spec.controls cpie cov nv1 cha chd

/-- Template: `images_tw` at the clean world, every per-table hypothesis by a finite check. -/
theorem images_tw_world {specCaller : AdmissibleCaller rho}
    {spec : ArmCert.Translate.Model.TopologyImageSpec (fun q => ∃ q0 ∈ HeapWorldTables.queries, ArmCertWalk.SamePage q0.va q.va)}
    (sspec : SourceSpec rho specCaller spec) (hir : spec.imageRows = HeapWorldTables.tables.imageRows) :
    ArmCert.Translate.Model.CurrentImagesAt spec (sourceAttributes rho caller) W.rows
        (ArmBridge.CruxGenGuarded.beforeFetchState (worldEntry worldSemantics rho caller W pcount)) ∧
      ArmCertWalk.RawImageAt spec.imageRows
        (ArmBridge.CruxGenGuarded.beforeFetchState (worldEntry worldSemantics rho caller W pcount)).mem :=
  images_tw rho caller pcount W HeapWorldTables.tables rfl
    (by unfold ArmCert.Translate.Model.PermissionRowsDeclared; decide) (by decide) (by decide)
    (fun b => by cases b <;> decide) (by decide)
    (fun c h1 h2 h3 h4 h5 => by
      simp only [checkPermissionImageNoOverlay, permissionParamsView, imageParamsLit,
        ArmCertWalk.descriptorPermissionView, S1LogicalReference.leafPermissions,
        S1LogicalReference.classicPermissions, h1, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte]
      decide)
    sspec hir

/-- The no-update parameters at their source values (HAFT 0: FEAT_HAFT absent). -/
def noUpdateParamsLit : ArmFull.S1TTWParams :=
  { (default : ArmFull.S1TTWParams) with ha := 1#1, hd := 1#1, pie := 0#1, haft := 0#1 }

#check "CURRENT_DECL GB10.Heap.Variant.a211_tw"
theorem a211_tw (t : TopologyTables domain)
    (hnoupd : ∀ wr : Bool, ArmCertWalk.NoUpdateRows noUpdateParamsLit (noUpdateAccessView wr) t.imageRows = true)
    {spec : ArmCert.Translate.Model.TopologyImageSpec domain}
    {specCaller : AdmissibleCaller rho} (sspec : SourceSpec rho specCaller spec)
    (hir : spec.imageRows = t.imageRows) :
    CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/noUpd" (∀ (wr : Bool) (acc : ArmFull.AccessDescriptor), ArmCert.Translate.Model.DataShape wr acc → ArmCertWalk.NoUpdateRows (have __src := spec.params; { ha := __src.ha, hd := __src.hd, tbi := __src.tbi, tbid := __src.tbid, nfd := __src.nfd, e0pd := __src.e0pd, d128 := __src.d128, aie := __src.aie, mair2 := __src.mair2, ds := __src.ds, ps := __src.ps, txsz := __src.txsz, epan := __src.epan, dct := __src.dct, nv1 := __src.nv1, cmow := __src.cmow, pnch := __src.pnch, disch := __src.disch, haft := ArmCert.Translate.Model.hostHAFT (worldEntry worldSemantics rho caller w pcount).regs, mtx := __src.mtx, skl := __src.skl, pie := __src.pie, pir := __src.pir, pire0 := __src.pire0, emec := __src.emec, amec := __src.amec, t0sz := __src.t0sz, t1sz := __src.t1sz, uwxn := __src.uwxn, tgx := __src.tgx, irgn := __src.irgn, orgn := __src.orgn, sh := __src.sh, hpd := __src.hpd, ee := __src.ee, wxn := __src.wxn, ntlsmd := __src.ntlsmd, dc := __src.dc, sif := __src.sif, mair := __src.mair }) acc spec.imageRows = true) := by
  obtain ⟨ha, hd, pie, -⟩ := sourceSpec_walkLiterals rho specCaller sspec (worldPayload W pcount).data
  have f189 := sourceRegs_feature rho caller (worldPayload w pcount).data 189 (by decide) false _ rfl
  refine ⟨noUpd_of_view _ _ (fun wr => ?_)⟩
  have haft : ArmCert.Translate.Model.hostHAFT (worldEntry worldSemantics rho caller w pcount).regs = 0#1 := by
    unfold ArmCert.Translate.Model.hostHAFT
    show (if (sourceRegs rho caller (worldPayload w pcount).data).FeatureImpl[189] && _ && _ then _ else _) = _
    rw [f189]
    rfl
  have view : noUpdateParamsView { spec.params with haft := ArmCert.Translate.Model.hostHAFT (worldEntry worldSemantics rho caller w pcount).regs } =
      noUpdateParamsLit := by
    simp only [noUpdateParamsView, noUpdateParamsLit, ha, hd, pie, haft]
  rw [show noUpdateParamsView _ = noUpdateParamsLit from view, hir]
  exact hnoupd wr

end tableGeneric

end ReleaseProfile.GB10.Heap.Variant

#print axioms ReleaseProfile.GB10.Heap.Variant.images
#print axioms ReleaseProfile.GB10.Heap.Variant.a264
#print axioms ReleaseProfile.GB10.Heap.Variant.images_tw
