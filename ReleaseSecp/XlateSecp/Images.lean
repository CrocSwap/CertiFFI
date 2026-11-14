import XlateSecp.Raw
import ReleaseProfile.GB10.HeapImages

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

/-!
# Secp image leaves at the source-built entry (Translate, next train; speed mode)

Card leaves a79-a83 at `raw := Raw.Ro sem rho caller c pcount o` (the canonical raw), `rows := World.permissionRows`, the World entry:
 Heap image proofs (HeapC2Normal `world_images`, `checkAttr_world`, `checkWB_world`) at the secp World.
Walk params/controls via `sourceSpec_walkLiterals` on `Raw.R_source`; MAIR/XS via `sourceAttributes_mair/xs`;
memory via `World.entry_realizes_table`.
-/

namespace XlateSecp.Images

open ReleaseProfile.MachineSource ReleaseProfile.GB10 TranslateSpan ArmCert.Translate.Model

variable (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
  (c : World.Card) (pcount : BitVec 88)

/-- Shorthand for the World entry. -/
abbrev E : ArmBridge.Draft.NativeState := World.entry sem rho caller c pcount

theorem wxn_lit {domain : QueryDomain} {spec : TopologyImageSpec domain}
    (sspec : SourceSpec rho caller spec) (d : DataPart) : spec.params.wxn = 0#1 := by
  rw [sspec.paramsWxn d, sourceRegs_bank64 rho caller d .SCTLR_EL2]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_SCTLR_EL2_Type_WXN, Sail.BitVec.extractLsb, BitVec.getLsbD_extractLsb] at hj ⊢
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using
    rho.property.construction.control64 caller.caller .SCTLR_EL2 ⟨19, by decide⟩ false _ rfl rfl

theorem controls_ha_lit {domain : QueryDomain} {spec : TopologyImageSpec domain}
    (sspec : SourceSpec rho caller spec) (d : DataPart) : spec.controls.ha = true := by
  rw [sspec.ha d, ← sspec.paramsHa d, (sourceSpec_walkLiterals rho caller sspec d).1]
  rfl

theorem controls_hd_lit {domain : QueryDomain} {spec : TopologyImageSpec domain}
    (sspec : SourceSpec rho caller spec) (d : DataPart) : spec.controls.hd = true := by
  rw [sspec.hd d, ← sspec.paramsHd d, (sourceSpec_walkLiterals rho caller sspec d).2.1]
  rfl

theorem off_before :
    ArmCertWalk.e0OverlayEnabled (ArmBridge.CruxGenGuarded.beforeFetchState (E sem rho caller c pcount)).regs = false := by
  rw [beforeFetch_regs]
  exact e0Overlay_source rho caller (World.payload c pcount).data

theorem checkAttr_world :
    checkAttributeImage World.imageRows (sourceAttributes rho caller) = true := by
  have h : checkAttributeImage World.imageRows (sourceAttributes rho caller) =
      World.imageRows.all (fun row => !row.leaf || decide (ArmCertWalk.reservedAttribute
        (sourceAttributes rho caller).xs (sourceAttributes rho caller).mte2
        (ArmCertWalk.mairByte (sourceAttributes rho caller).mair (ArmCertWalk.descriptorIndex row.raw)) = false)) :=
    rfl
  rw [h, sourceAttributes_mair rho caller, sourceAttributes_xs rho caller]
  generalize (sourceAttributes rho caller).mte2 = b
  cases b <;> decide

theorem checkWB_world :
    checkWriteBackAttributeImage World.imageRows (sourceAttributes rho caller) = true := by
  have h : checkWriteBackAttributeImage World.imageRows (sourceAttributes rho caller) =
      World.imageRows.all (fun row => !row.leaf || writeBackByte
        (ArmCertWalk.mairByte (sourceAttributes rho caller).mair (ArmCertWalk.descriptorIndex row.raw))) :=
    rfl
  rw [h, sourceAttributes_mair rho caller]
  decide

section leaves

variable {o : OracleChoice} {addrs : List (BitVec 64)} (h : CheckedTopology.check (Raw.Ro sem rho caller c pcount o) addrs 4 = true)


/-- The checked spec over the source-pinned raw. -/
noncomputable abbrev S := CheckedTopology.spec (Raw.Ro sem rho caller c pcount o) addrs 4 h

theorem S_imageRows : (S sem rho caller c pcount h).imageRows = World.imageRows := rfl

/-- a79: permission rows cover the image footprint. -/
theorem a79 : checkPermissionRowsCovered World.permissionRows (rowsFootprint (S sem rho caller c pcount h).imageRows) = true := by
  rw [S_imageRows]; decide

/-- a81: attribute image at the source attributes. -/
theorem a81 : checkAttributeImage (S sem rho caller c pcount h).imageRows (sourceAttributes rho caller) = true := by
  rw [S_imageRows]; exact checkAttr_world rho caller

/-- a82: write-back attribute image at the source attributes. -/
theorem a82 : checkWriteBackAttributeImage (S sem rho caller c pcount h).imageRows (sourceAttributes rho caller) = true := by
  rw [S_imageRows]; exact checkWB_world rho caller

/-- a80: descriptor bytes in the entry memory, at the source walk literals. -/
theorem a80 : checkImage (S sem rho caller c pcount h).imageRows ((S sem rho caller c pcount h).params.pie == 1#1)
    ((S sem rho caller c pcount h).params.ha == 1#1) ((S sem rho caller c pcount h).params.hd == 1#1)
    (ArmBridge.CruxGenGuarded.beforeFetchState (E sem rho caller c pcount)).mem = true := by
  have sspec := Raw.Ro_source sem rho caller c pcount o addrs h
  obtain ⟨ha, hd, pie, -⟩ := sourceSpec_walkLiterals rho caller sspec (World.payload c pcount).data
  refine (checkImage_of_satisfies (World.entry_realizes_table sem rho caller c pcount) ?_).trans ?_
  · intro x hx; rw [S_imageRows] at hx; exact hx
  · rw [S_imageRows, pie, ha, hd]; decide

/-- a83: permission image at the entry (no overlay; literal params view). -/
theorem a83 : checkPermissionImage World.permissionRows (S sem rho caller c pcount h).params
    (ArmBridge.CruxGenGuarded.beforeFetchState (E sem rho caller c pcount)).regs (S sem rho caller c pcount h).controls
    (ArmBridge.CruxGenGuarded.beforeFetchState (E sem rho caller c pcount)).mem = true := by
  have sspec := Raw.Ro_source sem rho caller c pcount o addrs h
  obtain ⟨ha, hd, pie, -, -, -, -, -, -, cpie, -⟩ := sourceSpec_walkLiterals rho caller sspec (World.payload c pcount).data
  have wxn := wxn_lit rho caller sspec (World.payload c pcount).data
  have cha := controls_ha_lit rho caller sspec (World.payload c pcount).data
  have chd := controls_hd_lit rho caller sspec (World.payload c pcount).data
  have cov := (sspec.overlay (World.payload c pcount).data).trans (overlay_source rho caller _)
  have nv1 := nv1Mode_el20 (S sem rho caller c pcount h).controls sspec.regime
  have hm : (ArmBridge.CruxGenGuarded.beforeFetchState (E sem rho caller c pcount)).mem =
      (World.entry sem rho caller c pcount).mem := rfl
  have offE : ArmCertWalk.e0OverlayEnabled (World.entry sem rho caller c pcount).regs = false :=
    e0Overlay_source rho caller (World.payload c pcount).data
  rw [hm, checkPermissionImage_of_satisfies (World.entry_realizes_table sem rho caller c pcount)
      (show ∀ x ∈ imageRowsPlan (S sem rho caller c pcount h).imageRows, x ∈ World.tablePlan from fun x hx => hx)
      (show PermissionRowsDeclared World.permissionRows (S sem rho caller c pcount h).imageRows by
        rw [S_imageRows]; unfold PermissionRowsDeclared; decide),
    checkPermissionImagePure_view _ _ _ (World.entry sem rho caller c pcount).regs _
      (off_before sem rho caller c pcount) offE,
    checkPermissionImagePure_noOverlay _ _ _ _ offE]
  simp only [checkPermissionImageNoOverlay, permissionParamsView, ha, hd, pie, wxn,
    ArmCertWalk.descriptorPermissionView, S1LogicalReference.leafPermissions,
    S1LogicalReference.classicPermissions, nv1, cpie, cha, chd, cov, Bool.false_eq_true, ↓reduceIte]
  decide

end leaves

end XlateSecp.Images

#print axioms XlateSecp.Images.a80
#print axioms XlateSecp.Images.a83
