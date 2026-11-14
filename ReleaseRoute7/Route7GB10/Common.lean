-- Route 7 positive-C2 world (loops): case-independent pieces: page-keyed topology tables, oracle, world registers of
-- the model entry, the source-pinned image/attribute checks, and the closed membership of a route-7 consumer map at the
-- world registers (SpanMap.closed from the per-page representatives of Route7GB10.Closed).
import Route7GB10.Closed
import Route7GB10.Plan
import ReleaseProfile.GB10.WorldSemantics
import ReleaseProfile.GB10.TablesBuilder
import ArmCertLoop.SpanMap
import ArmCertLoop.Image
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace Route7GB10
open ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ReleaseProfile.MachineSource ReleaseProfile.GB10
open ArmCertLoop Route7GB10.Closed

theorem queries_ok : World.queries.all
    (ArmCertWalk.checkSpecQuery gb10Physical World.layout World.logicalRows World.imageRows 4) = true := by decide

noncomputable def tables : TopologyTables (fun q => ∃ q0 ∈ World.queries, ArmCertWalk.SamePage q0.va q.va) :=
  TablesBuilder.tablesOfChecksPage World.layout World.logicalRows World.imageRows World.queries 4 World.spec_rows queries_ok

def oracle : OracleChoice where
  dc := 0#1
  dct := 0#1
  nv1 := 0#1
  t0sz := 0#3
  t1sz := 0#3
  uwxn := 0#1
  mair2 := 0
  pir := 0
  pire0 := 0
  controlsMair2 := 0#64
  controlsUwxn := false

/-- The 43 reviewed code VAs at B (0x4001a4 + 4i). -/
theorem codeVAs_eq : Image.codeVAs Plan.B Generated.imageStart Generated.imageWords = [0x4001a4#64, 0x4001a8#64, 0x4001ac#64, 0x4001b0#64, 0x4001b4#64, 0x4001b8#64, 0x4001bc#64, 0x4001c0#64, 0x4001c4#64, 0x4001c8#64, 0x4001cc#64, 0x4001d0#64, 0x4001d4#64, 0x4001d8#64, 0x4001dc#64, 0x4001e0#64, 0x4001e4#64, 0x4001e8#64, 0x4001ec#64, 0x4001f0#64, 0x4001f4#64, 0x4001f8#64, 0x4001fc#64, 0x400200#64, 0x400204#64, 0x400208#64, 0x40020c#64, 0x400210#64, 0x400214#64, 0x400218#64, 0x40021c#64, 0x400220#64, 0x400224#64, 0x400228#64, 0x40022c#64, 0x400230#64, 0x400234#64, 0x400238#64, 0x40023c#64, 0x400240#64, 0x400244#64, 0x400248#64, 0x40024c#64] := by decide

section
variable (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)

theorem checkAttr_world : checkAttributeImage World.imageRows (sourceAttributes rho caller) = true := by
  have h : checkAttributeImage World.imageRows (sourceAttributes rho caller) =
      World.imageRows.all (fun row => !row.leaf || decide (ArmCertWalk.reservedAttribute
        (sourceAttributes rho caller).xs (sourceAttributes rho caller).mte2
        (ArmCertWalk.mairByte (sourceAttributes rho caller).mair (ArmCertWalk.descriptorIndex row.raw)) = false)) :=
    rfl
  rw [h, sourceAttributes_mair rho caller, sourceAttributes_xs rho caller]
  generalize (sourceAttributes rho caller).mte2 = b
  cases b <;> decide

theorem checkWB_world : checkWriteBackAttributeImage World.imageRows (sourceAttributes rho caller) = true := by
  have h : checkWriteBackAttributeImage World.imageRows (sourceAttributes rho caller) =
      World.imageRows.all (fun row => !row.leaf || writeBackByte
        (ArmCertWalk.mairByte (sourceAttributes rho caller).mair (ArmCertWalk.descriptorIndex row.raw))) :=
    rfl
  rw [h, sourceAttributes_mair rho caller]
  decide

variable {domain : QueryDomain} {spec : TopologyImageSpec domain}

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
end

/-! ## The model entry of a route-7 case -/

section entry
variable (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
  (gprs : Vector (BitVec 64) 31) (entry : Nat) (pcount : BitVec 88)

noncomputable abbrev E : ArmBridge.Draft.NativeState :=
  makeModelEntry worldSemantics rho caller (Plan.payload gprs entry pcount)

theorem sat : NativeSourceInit.Satisfies Plan.plan (E rho caller gprs entry pcount).mem :=
  Plan.realizes worldSemantics rho caller gprs entry pcount

theorem worldRegs :
    WorldRegs (E rho caller gprs entry pcount).regs
      (controlWord rho.val caller.caller .TCR_EL2) (controlWord rho.val caller.caller .SCTLR_EL2) := by
  have hd : (E rho caller gprs entry pcount).regs = sourceRegs rho caller (Plan.payload gprs entry pcount).data := rfl
  rw [hd]
  refine ⟨rfl, rfl, by simp [sourceRegs, sourceBank64, Plan.payload, Plan.entryData]; first | rfl | decide | simp [isEntryData64],
    sourceRegs_bank64 rho caller _ .TCR_EL2, sourceRegs_bank64 rho caller _ .SCTLR_EL2,
    sourceRegs_feature rho caller _ 227 (by decide) false _ rfl,
    sourceRegs_feature rho caller _ 81 (by decide) true _ rfl,
    sourceRegs_feature rho caller _ 101 (by decide) true _ rfl, rfl, ?_, ?_, ?_⟩
  · bit1 .TCR_EL2 7 false
  · bit1 .SCTLR_EL2 12 true
  · bit1 .SCTLR_EL2 2 true

theorem off_before :
    ArmCertWalk.e0OverlayEnabled (ArmBridge.CruxGenGuarded.beforeFetchState (E rho caller gprs entry pcount)).regs = false := by
  have h : ArmCertWalk.e0OverlayEnabled (E rho caller gprs entry pcount).regs = false :=
    e0Overlay_source rho caller (Plan.payload gprs entry pcount).data
  rw [beforeFetch_regs]
  exact h

theorem world_images {domain : QueryDomain} {spec : TopologyImageSpec domain}
    (sspec : SourceSpec rho caller spec) (hir : spec.imageRows = World.imageRows) :
    CurrentImagesAt spec (sourceAttributes rho caller) World.permissionRows
        (ArmBridge.CruxGenGuarded.beforeFetchState (E rho caller gprs entry pcount)) ∧
      ArmCertWalk.RawImageAt spec.imageRows (ArmBridge.CruxGenGuarded.beforeFetchState (E rho caller gprs entry pcount)).mem := by
  obtain ⟨ha, hd, pie, -, -, -, -, -, -, cpie, -⟩ :=
    sourceSpec_walkLiterals rho caller sspec (Plan.payload gprs entry pcount).data
  have wxn := wxn_lit rho caller sspec (Plan.payload gprs entry pcount).data
  have cha := controls_ha_lit rho caller sspec (Plan.payload gprs entry pcount).data
  have chd := controls_hd_lit rho caller sspec (Plan.payload gprs entry pcount).data
  have cov := (sspec.overlay (Plan.payload gprs entry pcount).data).trans (overlay_source rho caller _)
  have nv1 := nv1Mode_el20 spec.controls sspec.regime
  refine images_of_checks spec (sourceAttributes rho caller) World.permissionRows _
    (plan := Plan.plan) (sat rho caller gprs entry pcount) ?_ ?_ ?_ ?_ ?_ ?_ _
    (off_before rho caller gprs entry pcount) (off_before rho caller gprs entry pcount) ?_
  · intro x hx
    rw [hir] at hx
    exact List.mem_append_left _ (List.mem_append_right _ hx)
  · rw [hir]; unfold PermissionRowsDeclared; decide
  · rw [hir]; decide
  · rw [hir, pie, ha, hd]; decide
  · rw [hir]; exact checkAttr_world rho caller
  · rw [hir]; exact checkWB_world rho caller
  · rw [checkPermissionImagePure_noOverlay _ _ _ _ (off_before rho caller gprs entry pcount)]
    simp only [checkPermissionImageNoOverlay, permissionParamsView, ha, hd, pie, wxn,
      ArmCertWalk.descriptorPermissionView, S1LogicalReference.leafPermissions,
      S1LogicalReference.classicPermissions, nv1, cpie, cha, chd, cov, Bool.false_eq_true, ↓reduceIte]
    decide

theorem noUpd {domain : QueryDomain} {spec : TopologyImageSpec domain}
    (sspec : SourceSpec rho caller spec) (hir : spec.imageRows = World.imageRows) :
    ∀ (wr : Bool) (acc : ArmFull.AccessDescriptor), DataShape wr acc →
      ArmCertWalk.NoUpdateRows { spec.params with haft := hostHAFT (E rho caller gprs entry pcount).regs }
        acc spec.imageRows = true := by
  obtain ⟨ha, hd, pie, -⟩ := sourceSpec_walkLiterals rho caller sspec (Plan.payload gprs entry pcount).data
  have f189 := sourceRegs_feature rho caller (Plan.payload gprs entry pcount).data 189 (by decide) false _ rfl
  refine noUpd_of_view _ _ (fun w => ?_)
  simp only [noUpdateParamsView, ha, hd, pie]
  have haft : hostHAFT (E rho caller gprs entry pcount).regs = 0#1 := by
    unfold hostHAFT
    show (if (sourceRegs rho caller (Plan.payload gprs entry pcount).data).FeatureImpl[189] && _ && _ then _ else _) = _
    rw [f189]
    rfl
  rw [haft, hir]
  cases w <;> decide
end entry

/-! ## Closed membership of a route-7 consumer map over (d, s) at the world registers -/

theorem closed_spans {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho} {domain : QueryDomain}
    {spec : TopologyImageSpec domain} (w : WorldSpec spec)
    (hdom : ∀ q : AccessQuery, (∃ q0 ∈ World.queries, ArmCertWalk.SamePage q0.va q.va) → domain q)
    (state : ArmCertWalk.State) {tcr sctlr : BitVec 64} (r : WorldRegs state.regs tcr sctlr)
    (ss : List SpanMap.Span)
    (hss : ∀ span ∈ ss, span.length = 1 ∧ (span.base = 0x30000#64 ∨ span.base = 0x31000#64)) :
    ClosedMembershipAt spec (sourceAttributes rho caller) World.permissionRows World.mapping
      (SpanMap.consumerMap ss (Image.codeVAs Plan.B Generated.imageStart Generated.imageWords) World.mapping
        (rowsFootprint World.imageRows).byte) state := by
  let rR : List (ClosedPages.Representative spec (sourceAttributes rho caller) World.permissionRows World.queries (DataShape false)) := [rep_srcRead w, rep_dstRead w]
  let rW : List (ClosedPages.Representative spec (sourceAttributes rho caller) World.permissionRows World.queries (DataShape true)) := [rep_srcWrite w, rep_dstWrite w]
  let rF : List (ClosedPages.Representative spec (sourceAttributes rho caller) World.permissionRows World.queries FetchShape) := [rep_fetch400000 w]
  have lR : ∀ x ∈ rR, x.level = 3 := by intro x hx; simp only [rR, List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> rfl
  have lW : ∀ x ∈ rW, x.level = 3 := by intro x hx; simp only [rW, List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> rfl
  have lF : ∀ x ∈ rF, x.level = 3 := by intro x hx; simp only [rF, List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> rfl
  have hR : [0x30000#64, 0x31000#64].all (fun va => ClosedPages.accessOK spec (sourceAttributes rho caller) World.permissionRows World.mapping rR state.regs va 1) = true := by
    simp only [rR, List.all_cons, List.all_nil, Bool.and_true]
    all_goals acc_ok
  have hW : [0x30000#64, 0x31000#64].all (fun va => ClosedPages.accessOK spec (sourceAttributes rho caller) World.permissionRows World.mapping rW state.regs va 1) = true := by
    simp only [rW, List.all_cons, List.all_nil, Bool.and_true]
    all_goals acc_ok
  have hc : (Image.codeVAs Plan.B Generated.imageStart Generated.imageWords).all (fun va => ClosedPages.accessOK spec (sourceAttributes rho caller) World.permissionRows World.mapping rF state.regs va 4) = true := by
    rw [codeVAs_eq]
    simp only [rF, List.all_cons, List.all_nil, Bool.and_true]
    all_goals acc_ok
  have dataVA : ∀ span ∈ ss, ∀ i, i < span.length → SpanMap.byteVA span i ∈ [0x30000#64, 0x31000#64] := by
    intro span hs i hi
    obtain ⟨len, hb⟩ := hss span hs
    have : i = 0 := by omega
    subst this
    simp only [SpanMap.byteVA, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rcases hb with hb | hb <;> simp [hb]
  have dataOK : ∀ span ∈ ss, ∀ i, i < span.length → (if span.write then
      ClosedPages.accessOK spec (sourceAttributes rho caller) World.permissionRows World.mapping rW state.regs (SpanMap.byteVA span i) 1
      else ClosedPages.accessOK spec (sourceAttributes rho caller) World.permissionRows World.mapping rR state.regs (SpanMap.byteVA span i) 1) = true := by
    intro span hs i hi
    have m := dataVA span hs i hi
    cases span.write
    · exact List.all_eq_true.1 hR _ m
    · exact List.all_eq_true.1 hW _ m
  refine SpanMap.closed spec _ _ _ ss _ _ state ?_ ?_ ?_
  · intro va acc aligned size permitted
    rcases permitted.2 with ⟨span, m, i, room, hva, hsize, shape⟩ | ⟨m, hsize, shape⟩
    · have h := dataOK span m i room
      subst hva; subst hsize
      cases hw : span.write <;> simp only [hw, Bool.false_eq_true, ite_false, ite_true] at h
      · exact hdom _ (ClosedPages.access_case_pages spec _ _ _ rR lR state.regs _ _ h state rfl).1
      · exact hdom _ (ClosedPages.access_case_pages spec _ _ _ rW lW state.regs _ _ h state rfl).1
    · subst hsize
      exact hdom _ (ClosedPages.access_case_pages spec _ _ _ rF lF state.regs _ _ (List.all_eq_true.1 hc va m) state rfl).1
  · intro span m i room
    have h := dataOK span m i room
    cases hw : span.write <;> simp only [hw, Bool.false_eq_true, ite_false, ite_true] at h
    · obtain ⟨_, r, data, rshape, _, current⟩ := ClosedPages.access_case_pages spec _ _ _ rR lR state.regs _ _ h state rfl
      exact ⟨r, data, hw ▸ rshape, current⟩
    · obtain ⟨_, r, data, rshape, _, current⟩ := ClosedPages.access_case_pages spec _ _ _ rW lW state.regs _ _ h state rfl
      exact ⟨r, data, hw ▸ rshape, current⟩
  · intro va m
    obtain ⟨_, r, data, rshape, _, current⟩ := ClosedPages.access_case_pages spec _ _ _ rF lF state.regs _ _ (List.all_eq_true.1 hc va m) state rfl
    exact ⟨r, data, rshape, current⟩

end Route7GB10
#print axioms Route7GB10.world_images
#print axioms Route7GB10.noUpd
#print axioms Route7GB10.closed_spans
