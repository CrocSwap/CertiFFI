import ReleaseProfile.GB10.HeapWorldData
import ReleaseProfile.GB10.HeapImages
import Bridge.CruxGenGuarded.ConsumerMapShim
import ReleaseProfile.GB10.HeapF21World

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

/-!
# Worked Heap normal positive C2 at the concrete clean world (assembly, in progress)

Payload/program atoms of the residual at `worldEntry worldSemantics rho caller world pcount`.
-/

namespace ReleaseProfile.GB10.Heap.Normal

open ReleaseProfile.MachineSource ReleaseProfile.GB10 ReleaseProfile.GB10.Heap

abbrev W := HeapWorldData.world

variable (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (pcount : BitVec 88)

abbrev E := worldEntry worldSemantics rho caller W pcount

theorem budget_small : W.budget ≤ timersBudget := by decide

/-- The world's generic timers are disabled (entry data chosen quiet,). -/
theorem timers_disabled : TimersDisabled W.data.timers := by
  intro _ _
  show (0#64 : BitVec 64).getLsbD 0 = false
  decide

theorem a16 : CertiFFI.Claim.RunCheck "card:budget" (357 + 12 ≤ W.budget) := ⟨by decide⟩
theorem a17 : CertiFFI.Claim.RunCheck "card:plan-offsets" (∀ (j : Nat), (W.offS j).toNat % 4 = 0) :=
  ⟨HeapV2Card.Instance.rc_aligned⟩
theorem a18 : CertiFFI.Claim.RunCheck "card:plan-offsets"
    (∀ (j : Nat), j ≤ 6 → W.offS j = ArmBridge.CruxGenGuarded.Release.shimPC j) := ⟨HeapV2Card.Instance.rc_offPre⟩
theorem a19 : CertiFFI.Claim.RunCheck "card:plan-offsets"
    (∀ (j : Nat), 357 + 8 ≤ j → j ≤ 357 + 11 → W.offS j = ArmBridge.CruxGenGuarded.Release.shimPC (j - (357 + 1))) :=
  ⟨HeapV2Card.Instance.rc_offPost⟩
theorem a261 : CertiFFI.Claim.RunCheck "card:plan-offsets"
    (W.offS 7 = ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf 0) := ⟨HeapV2Card.Instance.rc_hoff⟩
theorem a245 : CertiFFI.Claim.RunCheck "card:default-image-binding" (W.image = ArmCert.Translate.Model.HeapV2.image W.base) := ⟨rfl⟩
theorem a246 : CertiFFI.Claim.RunCheck "card:default-load-base-binding" (W.loadBase = W.base) := ⟨rfl⟩

theorem a121 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pc"
    ((E rho caller pcount).regs._PC = W.base + W.offS 0) := by
  refine ⟨?_⟩
  show HeapWorldData.data._PC = HeapWorldData.base + HeapV2Card.Instance.offS 0
  rw [HeapV2Card.Instance.rc_offPre 0 (by decide)]
  decide

theorem a257 : CertiFFI.Claim.CallerContract "comp:caller:shim-caller-contract"
    ((E rho caller pcount).regs.SP_EL0 = BitVec.ofNat 64 W.pins.sp + BitVec.ofInt 64 16) := by
  refine ⟨?_⟩
  show HeapWorldData.data.SP_EL0 = _
  decide

theorem a259 : CertiFFI.Claim.CallerContract "comp:caller:caller-buffers" ((BitVec.ofNat 64 W.pins.sp).toNat % 16 = 0) :=
  ⟨by decide⟩

theorem a264 : CertiFFI.Claim.CallerContract "comp:caller:caller-buffers"
    (HeapV2StepCerts.RegBind.regVal (E rho caller pcount) (HeapV2StepCerts.RegBind.Reg.x 0) = BitVec.ofInt 64 ↑W.pins.x0) := by
  refine ⟨?_⟩
  simp only [HeapV2StepCerts.RegBind.regVal]
  show HeapWorldData.data.gpr[(0 : Fin 31).val] = _
  decide

theorem a265 : CertiFFI.Claim.CallerContract "comp:caller:caller-buffers"
    (HeapV2StepCerts.RegBind.regVal (E rho caller pcount) (HeapV2StepCerts.RegBind.Reg.x 1) = BitVec.ofInt 64 ↑W.pins.x1) := by
  refine ⟨?_⟩
  simp only [HeapV2StepCerts.RegBind.regVal]
  show HeapWorldData.data.gpr[(1 : Fin 31).val] = _
  decide

theorem a269 : CertiFFI.Claim.CallerContract "card:default-caller-return-low" ((E rho caller pcount).regs.gpr[30].toNat < 2 ^ 55) := by
  refine ⟨?_⟩
  show HeapWorldData.data.gpr[30].toNat < 2 ^ 55
  decide

theorem a270 : CertiFFI.Claim.CallerContract "card:default-caller-return-target"
    ((E rho caller pcount).regs.gpr[30] = W.base + W.offS 369) := by
  refine ⟨?_⟩
  show HeapWorldData.data.gpr[30] = HeapWorldData.base + HeapV2Card.Instance.offS 369
  decide

theorem a243 : CertiFFI.Claim.DeploymentObligation "card:default369-initial-tag-status-rows"
    (NativeMteTagCheck.TagStatusRows (E rho caller pcount) ((E rho caller pcount).choiceOcc.getD 1354 0) 112) :=
  ⟨world_tagStatusRows rho caller W pcount 112⟩

/-! ## Consumer-map agreement (atom 274) from finite mapping checks -/

def mappedB (mapping : BitVec 64 → Option Nat) (va : BitVec 64) : Bool :=
  match mapping va with
  | some pa => decide (pa < 2 ^ 56)
  | none => false

theorem mapped_of {mapping : BitVec 64 → Option Nat} {va : BitVec 64} (h : mappedB mapping va = true) :
    ∃ pa, mapping va = some pa ∧ pa < 2 ^ 56 := by
  unfold mappedB at h
  split at h
  · rename_i pa heq
    exact ⟨pa, heq, of_decide_eq_true h⟩
  · cases h

theorem shim_agrees_of_checks {domain : ArmCert.Translate.Model.QueryDomain}
    (spec : ArmCert.Translate.Model.TopologyImageSpec domain) (p : ArmCert.Translate.Model.HeapV2E17.Pins) (base : Nat)
    (mapping : BitVec 64 → Option Nat)
    (hd : ArmCert.Translate.Model.HeapV2Plan.symbolicAccesses.all
      (fun a => mappedB mapping (ArmCert.Translate.Model.HeapV2E17.dataVA p a)) = true)
    (hc : ArmCert.Translate.Model.HeapV2Plan.codeWords.all
      (fun c => mappedB mapping (ArmCert.Translate.Model.HeapV2E17.codeVA base c.1)) = true)
    (hs : ArmCert.Translate.Model.HeapV2ShimPlan.codeWords.all
      (fun c => mappedB mapping (ArmCert.Translate.Model.HeapV2E17.shimCodeVA base c.1)) = true)
    (hsp : mappedB mapping (BitVec.ofNat 64 p.sp) = true) :
    ArmCert.Translate.Model.ConsumerMapAgrees spec mapping
      (ArmCert.Translate.Model.HeapV2E17.consumerMapShim (fun _ => True) p base mapping
        (ArmCert.Translate.Model.rowsFootprint spec.imageRows).byte) := by
  apply ArmCert.Translate.Model.HeapV2E17.consumerShim_agrees
  intro va acc size permitted
  rcases permitted with (⟨access, member, _, hva, _, _⟩ | ⟨code, member, hva, _, _⟩) | ⟨code, member, hva, _, _⟩ |
      ⟨_, hva, _, _⟩
  · subst hva; exact mapped_of (List.all_eq_true.1 hd access member)
  · subst hva; exact mapped_of (List.all_eq_true.1 hc code member)
  · subst hva; exact mapped_of (List.all_eq_true.1 hs code member)
  · subst hva; exact mapped_of hsp

theorem world_data_mapped : ArmCert.Translate.Model.HeapV2Plan.symbolicAccesses.all
    (fun a => mappedB W.mapping (ArmCert.Translate.Model.HeapV2E17.dataVA W.pins a)) = true := by decide +kernel
theorem world_code_mapped : ArmCert.Translate.Model.HeapV2Plan.codeWords.all
    (fun c => mappedB W.mapping (ArmCert.Translate.Model.HeapV2E17.codeVA W.base.toNat c.1)) = true := by decide +kernel
theorem world_shim_mapped : ArmCert.Translate.Model.HeapV2ShimPlan.codeWords.all
    (fun c => mappedB W.mapping (ArmCert.Translate.Model.HeapV2E17.shimCodeVA W.base.toNat c.1)) = true := by decide +kernel
theorem world_sp_mapped : mappedB W.mapping (BitVec.ofNat 64 W.pins.sp) = true := by decide +kernel

theorem a274 {domain : ArmCert.Translate.Model.QueryDomain} (spec : ArmCert.Translate.Model.TopologyImageSpec domain) :
    CertiFFI.Claim.DeploymentObligation "card:consumer-map-agrees"
      (ArmCert.Translate.Model.ConsumerMapAgrees spec W.mapping
        (ArmBridge.CruxGenGuarded.Release.shimMap spec W.mapping W.base W.pins)) :=
  ⟨shim_agrees_of_checks spec W.pins W.base.toNat W.mapping world_data_mapped world_code_mapped world_shim_mapped
    world_sp_mapped⟩

/-! ## Image atoms (55-59, 210) at the world entry -/

section images

variable {domain : ArmCert.Translate.Model.QueryDomain} {spec : ArmCert.Translate.Model.TopologyImageSpec domain}

theorem wxn_lit (sspec : SourceSpec rho caller spec) (d : DataPart) : spec.params.wxn = 0#1 := by
  rw [sspec.paramsWxn d, sourceRegs_bank64 rho caller d .SCTLR_EL2]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_SCTLR_EL2_Type_WXN, Sail.BitVec.extractLsb, BitVec.getLsbD_extractLsb] at hj ⊢
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using
    rho.property.construction.control64 caller.caller .SCTLR_EL2 ⟨19, by decide⟩ false _ rfl rfl

theorem controls_ha_lit (sspec : SourceSpec rho caller spec) (d : DataPart) : spec.controls.ha = true := by
  rw [sspec.ha d, ← sspec.paramsHa d, (sourceSpec_walkLiterals rho caller sspec d).1]
  rfl

theorem controls_hd_lit (sspec : SourceSpec rho caller spec) (d : DataPart) : spec.controls.hd = true := by
  rw [sspec.hd d, ← sspec.paramsHd d, (sourceSpec_walkLiterals rho caller sspec d).2.1]
  rfl

theorem off_entry : ArmCertWalk.e0OverlayEnabled (E rho caller pcount).regs = false :=
  e0Overlay_source rho caller _

theorem off_before :
    ArmCertWalk.e0OverlayEnabled (ArmBridge.CruxGenGuarded.beforeFetchState (E rho caller pcount)).regs = false := by
  rw [beforeFetch_regs]
  exact off_entry rho caller pcount

theorem checkAttr_world :
    ArmCert.Translate.Model.checkAttributeImage HeapWorldTables.imageRows (sourceAttributes rho caller) = true := by
  have h : ArmCert.Translate.Model.checkAttributeImage HeapWorldTables.imageRows (sourceAttributes rho caller) =
      HeapWorldTables.imageRows.all (fun row => !row.leaf || decide (ArmCertWalk.reservedAttribute
        (sourceAttributes rho caller).xs (sourceAttributes rho caller).mte2
        (ArmCertWalk.mairByte (sourceAttributes rho caller).mair (ArmCertWalk.descriptorIndex row.raw)) = false)) :=
    rfl
  rw [h, sourceAttributes_mair rho caller, sourceAttributes_xs rho caller]
  generalize (sourceAttributes rho caller).mte2 = b
  cases b <;> decide

theorem checkWB_world :
    ArmCert.Translate.Model.checkWriteBackAttributeImage HeapWorldTables.imageRows (sourceAttributes rho caller) = true := by
  have h : ArmCert.Translate.Model.checkWriteBackAttributeImage HeapWorldTables.imageRows (sourceAttributes rho caller) =
      HeapWorldTables.imageRows.all (fun row => !row.leaf || ArmCert.Translate.Model.writeBackByte
        (ArmCertWalk.mairByte (sourceAttributes rho caller).mair (ArmCertWalk.descriptorIndex row.raw))) :=
    rfl
  rw [h, sourceAttributes_mair rho caller]
  decide

/-- `sspec` may pin the spec at any admitted caller (only caller-independent literals are read from it); the
entry is at `caller`. -/
theorem world_images {specCaller : AdmissibleCaller rho} (sspec : SourceSpec rho specCaller spec)
    (hir : spec.imageRows = HeapWorldTables.tables.imageRows) :
    ArmCert.Translate.Model.CurrentImagesAt spec (sourceAttributes rho caller) W.rows
        (ArmBridge.CruxGenGuarded.beforeFetchState (E rho caller pcount)) ∧
      ArmCertWalk.RawImageAt spec.imageRows (ArmBridge.CruxGenGuarded.beforeFetchState (E rho caller pcount)).mem := by
  obtain ⟨ha, hd, pie, -, -, -, -, -, -, cpie, -⟩ := sourceSpec_walkLiterals rho specCaller sspec (worldPayload W pcount).data
  have wxn := wxn_lit rho specCaller sspec (worldPayload W pcount).data
  have cha := controls_ha_lit rho specCaller sspec (worldPayload W pcount).data
  have chd := controls_hd_lit rho specCaller sspec (worldPayload W pcount).data
  have cov := (sspec.overlay (worldPayload W pcount).data).trans (overlay_source rho specCaller _)
  have nv1 := nv1Mode_el20 spec.controls sspec.regime
  refine images_of_checks spec (sourceAttributes rho caller) W.rows _ (plan := W.tablePlan)
    (world_realizes_table worldSemantics rho caller W pcount) ?_ ?_ ?_ ?_ ?_ ?_ _ (off_before rho caller pcount)
    (off_before rho caller pcount) ?_
  · intro x hx
    rw [hir] at hx
    exact hx
  · rw [hir]; unfold ArmCert.Translate.Model.PermissionRowsDeclared; decide
  · rw [hir]; decide
  · rw [hir, pie, ha, hd]; decide
  · rw [hir]; exact checkAttr_world rho caller
  · rw [hir]; exact checkWB_world rho caller
  · rw [checkPermissionImagePure_noOverlay _ _ _ _ (off_before rho caller pcount)]
    simp only [checkPermissionImageNoOverlay, permissionParamsView, ha, hd, pie, wxn,
      ArmCertWalk.descriptorPermissionView, S1LogicalReference.leafPermissions,
      S1LogicalReference.classicPermissions, nv1, cpie, cha, chd, cov, Bool.false_eq_true, ↓reduceIte]
    decide

end images

/-! ## Atom 211 (no hardware update on any declared row) -/

theorem a211 {domain : ArmCert.Translate.Model.QueryDomain} {spec : ArmCert.Translate.Model.TopologyImageSpec domain}
    {specCaller : AdmissibleCaller rho} (sspec : SourceSpec rho specCaller spec) (hir : spec.imageRows = HeapWorldTables.tables.imageRows) :
    CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/noUpd" (∀ (wr : Bool) (acc : ArmFull.AccessDescriptor), ArmCert.Translate.Model.DataShape wr acc → ArmCertWalk.NoUpdateRows (have __src := spec.params; { ha := __src.ha, hd := __src.hd, tbi := __src.tbi, tbid := __src.tbid, nfd := __src.nfd, e0pd := __src.e0pd, d128 := __src.d128, aie := __src.aie, mair2 := __src.mair2, ds := __src.ds, ps := __src.ps, txsz := __src.txsz, epan := __src.epan, dct := __src.dct, nv1 := __src.nv1, cmow := __src.cmow, pnch := __src.pnch, disch := __src.disch, haft := ArmCert.Translate.Model.hostHAFT (E rho caller pcount).regs, mtx := __src.mtx, skl := __src.skl, pie := __src.pie, pir := __src.pir, pire0 := __src.pire0, emec := __src.emec, amec := __src.amec, t0sz := __src.t0sz, t1sz := __src.t1sz, uwxn := __src.uwxn, tgx := __src.tgx, irgn := __src.irgn, orgn := __src.orgn, sh := __src.sh, hpd := __src.hpd, ee := __src.ee, wxn := __src.wxn, ntlsmd := __src.ntlsmd, dc := __src.dc, sif := __src.sif, mair := __src.mair }) acc spec.imageRows = true) := by
  obtain ⟨ha, hd, pie, -⟩ := sourceSpec_walkLiterals rho specCaller sspec (worldPayload W pcount).data
  have f189 := sourceRegs_feature rho caller (worldPayload W pcount).data 189 (by decide) false _ rfl
  refine ⟨noUpd_of_view _ _ (fun w => ?_)⟩
  simp only [noUpdateParamsView, ha, hd, pie]
  have haft : ArmCert.Translate.Model.hostHAFT (E rho caller pcount).regs = 0#1 := by
    unfold ArmCert.Translate.Model.hostHAFT
    show (if (sourceRegs rho caller (worldPayload W pcount).data).FeatureImpl[189] && _ && _ then _ else _) = _
    rw [f189]
    rfl
  rw [haft, hir]
  cases w <;> decide

/-! ## Atoms 266 (path selector) and 271 (data bytes linear) -/

theorem a266 : CertiFFI.Claim.CallerContract "card:path-selector"
    (HeapV2StepCerts.ValBind.NormalPath W.pins (HeapV2StepCerts.E17General.qOf (E rho caller pcount))) := by
  refine ⟨?_⟩
  simp only [HeapV2StepCerts.E17General.qOf, HeapV2StepCerts.RegBind.regVal]
  show HeapV2StepCerts.ValBind.NormalPath W.pins ⟨HeapWorldData.data.gpr[2], HeapWorldData.data.gpr[3]⟩
  unfold HeapV2StepCerts.ValBind.NormalPath
  decide

theorem a271 : CertiFFI.Claim.DeploymentObligation "card:default-mapping-no-double-map-pa"
    (TranslateMem.NoDoubleMapPA W.pins W.mapping) :=
  ⟨F21.ndPA_world⟩

/-! ## Final assembly -/

#check "CURRENT_DECL GB10.Heap.Normal.StaticsAt"
/-- The Translate-owned static atoms at the world entry (exact residual fields). -/
structure StaticsAt {domain : ArmCert.Translate.Model.QueryDomain} (spec : ArmCert.Translate.Model.TopologyImageSpec domain) : Prop where
  a20 : CertiFFI.Claim.DeploymentObligation "comp:caller:image-table-separated" (ArmCert.Translate.Model.ImageTableSeparated W.scope W.loadBase W.mapping (RtShim2.ShimMem.slotBytes W.pins W.mapping))
  a122 : CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/closed" (ArmCert.Translate.Model.ClosedMembershipAt spec (sourceAttributes rho caller) W.rows W.mapping (ArmBridge.CruxGenGuarded.Release.shimMap spec W.mapping W.base W.pins) (ArmBridge.CruxGenGuarded.beforeFetchState (E rho caller pcount)))
  a123 : CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/placed" (MemReloc.ImageOn W.scope W.image (E rho caller pcount) W.loadBase W.mapping)
  a244 : CertiFFI.Claim.DeploymentObligation "card:code-static" (RtDit.ShimFetch.ShimCodeStatic W.mapping W.base W.scope (ArmCert.Translate.Model.rowsFootprint spec.imageRows).byte)
  a256 : CertiFFI.Claim.DeploymentObligation "card:slot-present" (RtShim.SlotPrem.ShimSlotPresent W.pins W.mapping (E rho caller pcount))
  a258 : CertiFFI.Claim.DeploymentObligation "card:code-static" (RtShim.SlotPrem.ShimSlotStatic W.pins W.mapping (ArmCert.Translate.Model.rowsFootprint spec.imageRows))
  a260 : CertiFFI.Claim.DeploymentObligation "card:body-entry/S" (NativeBodyDeploy.BodyStatic spec W.mapping W.base W.pins)
  a262 : CertiFFI.Claim.DeploymentObligation "card:body-entry/hscope" (∀ (o : Nat), HeapV2StepCerts.codeScope o → W.scope o)
  a263 : CertiFFI.Claim.DeploymentObligation "card:body-entry/presentE" (HeapV2StepCerts.C3.DataPresent W.pins W.mapping (E rho caller pcount))
  a267 : CertiFFI.Claim.DeploymentObligation "comp:caller:image-table-separated" (ArmCert.Translate.Model.ImageTableSeparated W.scope W.base W.mapping (HeapV2StepCerts.Residue.StoreBytes W.pins W.mapping))
  a268 : CertiFFI.Claim.DeploymentObligation "card:default-slot-store-separation" (∀ (a : Nat), RtShim2.ShimMem.slotBytes W.pins W.mapping a → ¬HeapV2StepCerts.Residue.StoreBytes W.pins W.mapping a)
  a272 : CertiFFI.Claim.DeploymentObligation "card:default-functional-regions-injective" (ArmCertValue.HeapV2Mem.RegionsInjective W.pins W.mapping)
  a273 : CertiFFI.Claim.DeploymentObligation "card:default-functional-input-slot-separation" (∀ (i : Nat), i < 32 → ∀ (n : Nat), W.mapping (BitVec.ofNat 64 (W.pins.x1 + i)) = some n → ¬RtShim2.ShimMem.slotBytes W.pins W.mapping n)

#check "CURRENT_DECL GB10.Heap.Normal.StaticsAtP"
/-- F21: the Translate static atoms the card_normalP residual needs (no RegionsInjective / input-slot separation). -/
structure StaticsAtP {domain : ArmCert.Translate.Model.QueryDomain} (spec : ArmCert.Translate.Model.TopologyImageSpec domain) : Prop where
  a20 : CertiFFI.Claim.DeploymentObligation "comp:caller:image-table-separated" (ArmCert.Translate.Model.ImageTableSeparated W.scope W.loadBase W.mapping (RtShim2.ShimMem.slotBytes W.pins W.mapping))
  a122 : CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/closed" (ArmCert.Translate.Model.ClosedMembershipAt spec (sourceAttributes rho caller) W.rows W.mapping (ArmBridge.CruxGenGuarded.Release.shimMap spec W.mapping W.base W.pins) (ArmBridge.CruxGenGuarded.beforeFetchState (E rho caller pcount)))
  a123 : CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/placed" (MemReloc.ImageOn W.scope W.image (E rho caller pcount) W.loadBase W.mapping)
  a244 : CertiFFI.Claim.DeploymentObligation "card:code-static" (RtDit.ShimFetch.ShimCodeStatic W.mapping W.base W.scope (ArmCert.Translate.Model.rowsFootprint spec.imageRows).byte)
  a256 : CertiFFI.Claim.DeploymentObligation "card:slot-present" (RtShim.SlotPrem.ShimSlotPresent W.pins W.mapping (E rho caller pcount))
  a258 : CertiFFI.Claim.DeploymentObligation "card:code-static" (RtShim.SlotPrem.ShimSlotStatic W.pins W.mapping (ArmCert.Translate.Model.rowsFootprint spec.imageRows))
  a260 : CertiFFI.Claim.DeploymentObligation "card:body-entry/S" (NativeBodyDeploy.BodyStatic spec W.mapping W.base W.pins)
  a262 : CertiFFI.Claim.DeploymentObligation "card:body-entry/hscope" (∀ (o : Nat), HeapV2StepCerts.codeScope o → W.scope o)
  a263 : CertiFFI.Claim.DeploymentObligation "card:body-entry/presentE" (HeapV2StepCerts.C3.DataPresent W.pins W.mapping (E rho caller pcount))
  a267 : CertiFFI.Claim.DeploymentObligation "comp:caller:image-table-separated" (ArmCert.Translate.Model.ImageTableSeparated W.scope W.base W.mapping (HeapV2StepCerts.Residue.StoreBytes W.pins W.mapping))
  a268 : CertiFFI.Claim.DeploymentObligation "card:default-slot-store-separation" (∀ (a : Nat), RtShim2.ShimMem.slotBytes W.pins W.mapping a → ¬HeapV2StepCerts.Residue.StoreBytes W.pins W.mapping a)

#check "CURRENT_DECL GB10.Heap.Normal.heap_normal_c2_of_statics"
/-- Positive normal C2 for the worked Heap card at every admissible completion and caller, given the
Translate static atoms at the clean world. Every other residual atom is proved here. -/
theorem heap_normal_c2_of_statics (statics : ∀ (pcount : BitVec 88)
      (spec : ArmCert.Translate.Model.TopologyImageSpec
        (fun q => ∃ q0 ∈ HeapWorldTables.queries, ArmCertWalk.SamePage q0.va q.va)),
      SourceSpec rho caller spec → spec.layout = HeapWorldTables.tables.layout →
      spec.logicalRows = HeapWorldTables.tables.logicalRows →
      spec.imageRows = HeapWorldTables.tables.imageRows → StaticsAtP rho caller pcount spec) :
    NormalC2 rho caller :=
  normal_c2_of_world rho caller worldSemantics W (timers_disabled) HeapWorldTables.tables HeapWorldData.oracle
    (fun pcount spec sspec hlay hlr hir timers =>
      have imgs := world_images rho caller pcount sspec hir
      have st := statics pcount spec sspec hlay hlr hir
      {
        timers := timers,
        a16 := a16,
        a17 := a17,
        a18 := a18,
        a19 := a19,
        a20 := st.a20,
        a55 := ⟨imgs.1.covered⟩,
        a56 := ⟨imgs.1.topology⟩,
        a57 := ⟨imgs.1.attributes⟩,
        a58 := ⟨imgs.1.writeback⟩,
        a59 := ⟨imgs.1.permissions⟩,
        a121 := a121 rho caller pcount,
        a122 := st.a122,
        a123 := st.a123,
        a210 := ⟨imgs.2⟩,
        a211 := a211 rho caller pcount sspec hir,
        a243 := a243 rho caller pcount,
        a244 := st.a244,
        a245 := a245,
        a246 := a246,
        a256 := st.a256,
        a257 := a257 rho caller pcount,
        a258 := st.a258,
        a259 := a259,
        a260 := ⟨ReleaseProfile.GB10.BodyStaticR.ofFull st.a260.holds⟩,
        a261 := a261,
        a262 := st.a262,
        a263 := st.a263,
        a264 := a264 rho caller pcount,
        a265 := a265 rho caller pcount,
        a266 := a266 rho caller pcount,
        a267 := st.a267,
        a268 := st.a268,
        a269 := a269 rho caller pcount,
        a270 := a270 rho caller pcount,
        a271 := a271,
        a272 := ⟨F21.ndSlot_world⟩,
        a273 := ⟨F21.layout_world⟩,
        a274 := a274 spec
      })

end ReleaseProfile.GB10.Heap.Normal

#print axioms ReleaseProfile.GB10.Heap.Normal.heap_normal_c2_of_statics
