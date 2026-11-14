import XlateSecpAlt.Raw
import ReleaseProfile.GB10.HeapImages
import XlateSecp.Images

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

/-!
# Secp image leaves at the source-built entry (Translate, next train; speed mode)

Card leaves a79-a83 at `raw := XlateSecpAlt.Raw.Ro sem rho caller c pcount o` (the canonical raw), `rows := XlateSecp.World.permissionRows`, the World entry:
 Heap image proofs (HeapC2Normal `world_images`, `XlateSecp.Images.checkAttr_world`, `XlateSecp.Images.checkWB_world`) at the secp XlateSecp.World.
Walk params/controls via `sourceSpec_walkLiterals` on `XlateSecpAlt.Raw.R_source`; MAIR/XS via `sourceAttributes_mair/xs`;
memory via `XlateSecpAlt.World.entry_realizes_table`.
-/

namespace XlateSecpAlt.Images

open ReleaseProfile.MachineSource ReleaseProfile.GB10 TranslateSpan ArmCert.Translate.Model

variable (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
  (c : XlateSecp.World.Card) (pcount : BitVec 88)

/-- Shorthand for the World entry. -/
abbrev E : ArmBridge.Draft.NativeState := XlateSecpAlt.World.entry sem rho caller c pcount

theorem off_before :
    ArmCertWalk.e0OverlayEnabled (ArmBridge.CruxGenGuarded.beforeFetchState (E sem rho caller c pcount)).regs = false := by
  rw [beforeFetch_regs]
  exact e0Overlay_source rho caller (XlateSecpAlt.World.payload c pcount).data

section leaves

variable {o : OracleChoice} {addrs : List (BitVec 64)} (h : CheckedTopology.check (XlateSecpAlt.Raw.Ro sem rho caller c pcount o) addrs 4 = true)


/-- The checked spec over the source-pinned raw. -/
noncomputable abbrev S := CheckedTopology.spec (XlateSecpAlt.Raw.Ro sem rho caller c pcount o) addrs 4 h

theorem S_imageRows : (S sem rho caller c pcount h).imageRows = XlateSecp.World.imageRows := rfl

/-- a79: permission rows cover the image footprint. -/
theorem a79 : checkPermissionRowsCovered XlateSecp.World.permissionRows (rowsFootprint (S sem rho caller c pcount h).imageRows) = true := by
  rw [S_imageRows]; decide

/-- a81: attribute image at the source attributes. -/
theorem a81 : checkAttributeImage (S sem rho caller c pcount h).imageRows (sourceAttributes rho caller) = true := by
  rw [S_imageRows]; exact XlateSecp.Images.checkAttr_world rho caller

/-- a82: write-back attribute image at the source attributes. -/
theorem a82 : checkWriteBackAttributeImage (S sem rho caller c pcount h).imageRows (sourceAttributes rho caller) = true := by
  rw [S_imageRows]; exact XlateSecp.Images.checkWB_world rho caller

/-- a80: descriptor bytes in the entry memory, at the source walk literals. -/
theorem a80 : checkImage (S sem rho caller c pcount h).imageRows ((S sem rho caller c pcount h).params.pie == 1#1)
    ((S sem rho caller c pcount h).params.ha == 1#1) ((S sem rho caller c pcount h).params.hd == 1#1)
    (ArmBridge.CruxGenGuarded.beforeFetchState (E sem rho caller c pcount)).mem = true := by
  have sspec := XlateSecpAlt.Raw.Ro_source sem rho caller c pcount o addrs h
  obtain ⟨ha, hd, pie, -⟩ := sourceSpec_walkLiterals rho caller sspec (XlateSecpAlt.World.payload c pcount).data
  refine (checkImage_of_satisfies (XlateSecpAlt.World.entry_realizes_table sem rho caller c pcount) ?_).trans ?_
  · intro x hx; rw [S_imageRows] at hx; exact hx
  · rw [S_imageRows, pie, ha, hd]; decide

/-- a83: permission image at the entry (no overlay; literal params view). -/
theorem a83 : checkPermissionImage XlateSecp.World.permissionRows (S sem rho caller c pcount h).params
    (ArmBridge.CruxGenGuarded.beforeFetchState (E sem rho caller c pcount)).regs (S sem rho caller c pcount h).controls
    (ArmBridge.CruxGenGuarded.beforeFetchState (E sem rho caller c pcount)).mem = true := by
  have sspec := XlateSecpAlt.Raw.Ro_source sem rho caller c pcount o addrs h
  obtain ⟨ha, hd, pie, -, -, -, -, -, -, cpie, -⟩ := sourceSpec_walkLiterals rho caller sspec (XlateSecpAlt.World.payload c pcount).data
  have wxn := XlateSecp.Images.wxn_lit rho caller sspec (XlateSecpAlt.World.payload c pcount).data
  have cha := XlateSecp.Images.controls_ha_lit rho caller sspec (XlateSecpAlt.World.payload c pcount).data
  have chd := XlateSecp.Images.controls_hd_lit rho caller sspec (XlateSecpAlt.World.payload c pcount).data
  have cov := (sspec.overlay (XlateSecpAlt.World.payload c pcount).data).trans (overlay_source rho caller _)
  have nv1 := nv1Mode_el20 (S sem rho caller c pcount h).controls sspec.regime
  have hm : (ArmBridge.CruxGenGuarded.beforeFetchState (E sem rho caller c pcount)).mem =
      (XlateSecpAlt.World.entry sem rho caller c pcount).mem := rfl
  have offE : ArmCertWalk.e0OverlayEnabled (XlateSecpAlt.World.entry sem rho caller c pcount).regs = false :=
    e0Overlay_source rho caller (XlateSecpAlt.World.payload c pcount).data
  rw [hm, checkPermissionImage_of_satisfies (XlateSecpAlt.World.entry_realizes_table sem rho caller c pcount)
      (show ∀ x ∈ imageRowsPlan (S sem rho caller c pcount h).imageRows, x ∈ XlateSecp.World.tablePlan from fun x hx => hx)
      (show PermissionRowsDeclared XlateSecp.World.permissionRows (S sem rho caller c pcount h).imageRows by
        rw [S_imageRows]; unfold PermissionRowsDeclared; decide),
    checkPermissionImagePure_view _ _ _ (XlateSecpAlt.World.entry sem rho caller c pcount).regs _
      (off_before sem rho caller c pcount) offE,
    checkPermissionImagePure_noOverlay _ _ _ _ offE]
  simp only [checkPermissionImageNoOverlay, permissionParamsView, ha, hd, pie, wxn,
    ArmCertWalk.descriptorPermissionView, S1LogicalReference.leafPermissions,
    S1LogicalReference.classicPermissions, nv1, cpie, cha, chd, cov, Bool.false_eq_true, ↓reduceIte]
  decide

end leaves

end XlateSecpAlt.Images

#print axioms XlateSecpAlt.Images.a80
#print axioms XlateSecpAlt.Images.a83
