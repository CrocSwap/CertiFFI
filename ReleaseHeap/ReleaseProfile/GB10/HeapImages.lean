import ReleaseProfile.GB10.SpecWitness
import ReleaseProfile.GB10.Producers
import ArmCertTranslateModel.PlanChecks
import ArmCertTranslateModel.CanonicalAdmission
import ArmCertTranslateModel.CurrentImages
import ArmCertWalk.NoUpdatePath
import ArmCertTranslateModel.ClosedTable

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048

/-!
# Image atoms at a source-built entry: reduction to literal views

The permission-image check reads the walk parameters only through `ha`, `hd`, `pie` and `wxn`
(all pinned by `SourceSpec` to source literals), and the registers only through
`e0OverlayEnabled`, which is false at every source register file.
So it equals the same check at the four-field parameter view and any overlay-free register file.
-/

namespace ReleaseProfile.GB10

open ReleaseProfile.MachineSource

#check "CURRENT_DECL GB10.permissionParamsView"
/-- The only walk-parameter fields the permission-image check reads. -/
def permissionParamsView (p : ArmFull.S1TTWParams) : ArmFull.S1TTWParams :=
  { (default : ArmFull.S1TTWParams) with ha := p.ha, hd := p.hd, pie := p.pie, wxn := p.wxn }

#check "CURRENT_DECL GB10.checkPermissionImagePure_view"
theorem checkPermissionImagePure_view (rows : List ArmCert.Translate.Model.PermissionRow)
    (p : ArmFull.S1TTWParams) (regs other : ArmFull.Regs) (controls : S1LogicalReference.Controls)
    (off : ArmCertWalk.e0OverlayEnabled regs = false)
    (otherOff : ArmCertWalk.e0OverlayEnabled other = false) :
    ArmCert.Translate.Model.checkPermissionImagePure rows p regs controls =
      ArmCert.Translate.Model.checkPermissionImagePure rows (permissionParamsView p) other controls := by
  unfold ArmCert.Translate.Model.checkPermissionImagePure
  apply ArmCert.Translate.Model.all_congr_mem
  intro row _
  simp only [ArmCert.Translate.Model.PermissionRow.checkPure, ArmCert.Translate.Model.checkCanonicalAdmission,
    ArmCertWalk.computedControls, off, otherOff, ArmCertWalk.finishControls,
    ArmCert.Translate.Model.nativeAdmissionView, ArmCert.Translate.Model.el0AdmissionView,
    ArmCert.Translate.Model.admissionPermissionView, ArmCertWalk.nativePermissionProjection,
    ArmCertWalk.baseControls, ArmCertWalk.directControls, ArmCertWalk.permissionChecksPass,
    permissionParamsView, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  exact rfl

#check "CURRENT_DECL GB10.e0Overlay_source"
theorem e0Overlay_source (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (d : DataPart) :
    ArmCertWalk.e0OverlayEnabled (sourceRegs rho caller d) = false := by
  have h210 := sourceRegs_feature rho caller d 210 (by decide) false _ rfl
  unfold ArmCertWalk.e0OverlayEnabled
  simp only [h210, ite_true]

#check "CURRENT_DECL GB10.mair_source"
/-- the canonical MAIR_EL2 word is the literal Linux MAIR_EL1_SET value at every completion. -/
theorem mair_source (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) :
    controlWord rho.val caller.caller .MAIR_EL2 = 0x000000040044ffff#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  match i, hi with
  | 0, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨0, by decide⟩ true _ rfl rfl).trans (by decide)
  | 1, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨1, by decide⟩ true _ rfl rfl).trans (by decide)
  | 2, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨2, by decide⟩ true _ rfl rfl).trans (by decide)
  | 3, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨3, by decide⟩ true _ rfl rfl).trans (by decide)
  | 4, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨4, by decide⟩ true _ rfl rfl).trans (by decide)
  | 5, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨5, by decide⟩ true _ rfl rfl).trans (by decide)
  | 6, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨6, by decide⟩ true _ rfl rfl).trans (by decide)
  | 7, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨7, by decide⟩ true _ rfl rfl).trans (by decide)
  | 8, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨8, by decide⟩ true _ rfl rfl).trans (by decide)
  | 9, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨9, by decide⟩ true _ rfl rfl).trans (by decide)
  | 10, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨10, by decide⟩ true _ rfl rfl).trans (by decide)
  | 11, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨11, by decide⟩ true _ rfl rfl).trans (by decide)
  | 12, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨12, by decide⟩ true _ rfl rfl).trans (by decide)
  | 13, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨13, by decide⟩ true _ rfl rfl).trans (by decide)
  | 14, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨14, by decide⟩ true _ rfl rfl).trans (by decide)
  | 15, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨15, by decide⟩ true _ rfl rfl).trans (by decide)
  | 16, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨16, by decide⟩ false _ rfl rfl).trans (by decide)
  | 17, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨17, by decide⟩ false _ rfl rfl).trans (by decide)
  | 18, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨18, by decide⟩ true _ rfl rfl).trans (by decide)
  | 19, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨19, by decide⟩ false _ rfl rfl).trans (by decide)
  | 20, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨20, by decide⟩ false _ rfl rfl).trans (by decide)
  | 21, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨21, by decide⟩ false _ rfl rfl).trans (by decide)
  | 22, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨22, by decide⟩ true _ rfl rfl).trans (by decide)
  | 23, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨23, by decide⟩ false _ rfl rfl).trans (by decide)
  | 24, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨24, by decide⟩ false _ rfl rfl).trans (by decide)
  | 25, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨25, by decide⟩ false _ rfl rfl).trans (by decide)
  | 26, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨26, by decide⟩ false _ rfl rfl).trans (by decide)
  | 27, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨27, by decide⟩ false _ rfl rfl).trans (by decide)
  | 28, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨28, by decide⟩ false _ rfl rfl).trans (by decide)
  | 29, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨29, by decide⟩ false _ rfl rfl).trans (by decide)
  | 30, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨30, by decide⟩ false _ rfl rfl).trans (by decide)
  | 31, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨31, by decide⟩ false _ rfl rfl).trans (by decide)
  | 32, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨32, by decide⟩ false _ rfl rfl).trans (by decide)
  | 33, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨33, by decide⟩ false _ rfl rfl).trans (by decide)
  | 34, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨34, by decide⟩ true _ rfl rfl).trans (by decide)
  | 35, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨35, by decide⟩ false _ rfl rfl).trans (by decide)
  | 36, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨36, by decide⟩ false _ rfl rfl).trans (by decide)
  | 37, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨37, by decide⟩ false _ rfl rfl).trans (by decide)
  | 38, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨38, by decide⟩ false _ rfl rfl).trans (by decide)
  | 39, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨39, by decide⟩ false _ rfl rfl).trans (by decide)
  | 40, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨40, by decide⟩ false _ rfl rfl).trans (by decide)
  | 41, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨41, by decide⟩ false _ rfl rfl).trans (by decide)
  | 42, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨42, by decide⟩ false _ rfl rfl).trans (by decide)
  | 43, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨43, by decide⟩ false _ rfl rfl).trans (by decide)
  | 44, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨44, by decide⟩ false _ rfl rfl).trans (by decide)
  | 45, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨45, by decide⟩ false _ rfl rfl).trans (by decide)
  | 46, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨46, by decide⟩ false _ rfl rfl).trans (by decide)
  | 47, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨47, by decide⟩ false _ rfl rfl).trans (by decide)
  | 48, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨48, by decide⟩ false _ rfl rfl).trans (by decide)
  | 49, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨49, by decide⟩ false _ rfl rfl).trans (by decide)
  | 50, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨50, by decide⟩ false _ rfl rfl).trans (by decide)
  | 51, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨51, by decide⟩ false _ rfl rfl).trans (by decide)
  | 52, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨52, by decide⟩ false _ rfl rfl).trans (by decide)
  | 53, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨53, by decide⟩ false _ rfl rfl).trans (by decide)
  | 54, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨54, by decide⟩ false _ rfl rfl).trans (by decide)
  | 55, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨55, by decide⟩ false _ rfl rfl).trans (by decide)
  | 56, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨56, by decide⟩ false _ rfl rfl).trans (by decide)
  | 57, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨57, by decide⟩ false _ rfl rfl).trans (by decide)
  | 58, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨58, by decide⟩ false _ rfl rfl).trans (by decide)
  | 59, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨59, by decide⟩ false _ rfl rfl).trans (by decide)
  | 60, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨60, by decide⟩ false _ rfl rfl).trans (by decide)
  | 61, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨61, by decide⟩ false _ rfl rfl).trans (by decide)
  | 62, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨62, by decide⟩ false _ rfl rfl).trans (by decide)
  | 63, _ => exact (rho.property.construction.control64 caller.caller .MAIR_EL2 ⟨63, by decide⟩ false _ rfl rfl).trans (by decide)
  | n + 64, h => exact absurd h (by omega)

theorem sourceAttributes_mair (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) :
    (sourceAttributes rho caller).mair = 0x000000040044ffff#64 :=
  mair_source rho caller

theorem sourceAttributes_xs (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) :
    (sourceAttributes rho caller).xs = true :=
  FeatureSource.value_declared rho.val.features 166 true _ rfl

#check "CURRENT_DECL GB10.attributeImage_source"
/-- Atom shape `AttributeImage (rowsObserve rows) (sourceAttributes rho caller) mem` from the byte check and
an attribute check over every config with the literal MAIR and XS. -/
theorem attributeImage_source (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (rows : List ArmCert.Translate.Model.ImageRow) (params : ArmFull.S1TTWParams) (mem : ArmCert.Translate.Model.Mem)
    (bytes : ArmCert.Translate.Model.checkImage rows (params.pie == 1#1) (params.ha == 1#1) (params.hd == 1#1) mem = true)
    (check : ∀ c : ArmCertWalk.AttributeConfig, c.mair = 0x000000040044ffff#64 → c.xs = true →
      ArmCert.Translate.Model.checkAttributeImage rows c = true) :
    ArmCert.Translate.Model.AttributeImage (ArmCert.Translate.Model.rowsObserve rows) (sourceAttributes rho caller) mem :=
  ArmCert.Translate.Model.check_attribute_image_sound rows _ params mem bytes
    (check _ (sourceAttributes_mair rho caller) (sourceAttributes_xs rho caller))

#check "CURRENT_DECL GB10.writeBackImage_source"
theorem writeBackImage_source (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (rows : List ArmCert.Translate.Model.ImageRow) (params : ArmFull.S1TTWParams) (mem : ArmCert.Translate.Model.Mem)
    (bytes : ArmCert.Translate.Model.checkImage rows (params.pie == 1#1) (params.ha == 1#1) (params.hd == 1#1) mem = true)
    (check : ∀ c : ArmCertWalk.AttributeConfig, c.mair = 0x000000040044ffff#64 →
      ArmCert.Translate.Model.checkWriteBackAttributeImage rows c = true) :
    ArmCert.Translate.Model.WriteBackAttributeImage (ArmCert.Translate.Model.rowsObserve rows) (sourceAttributes rho caller) mem :=
  ArmCert.Translate.Model.check_writeback_attribute_image_sound rows _ params mem bytes
    (check _ (sourceAttributes_mair rho caller))

#check "CURRENT_DECL GB10.images_of_checks"
/-- Image atoms (covered/topology/attributes/writeback/permissions, and raw) on any state whose memory
satisfies a plan covering the declared descriptor bytes, from memory-free checks: the permission check
at the four-field params view and any overlay-free register file. -/
theorem images_of_checks {domain : ArmCert.Translate.Model.QueryDomain}
    (spec : ArmCert.Translate.Model.TopologyImageSpec domain) (config : ArmCertWalk.AttributeConfig)
    (rows : List ArmCert.Translate.Model.PermissionRow) (state : ArmCert.Translate.Model.State)
    {plan : NativeSourceInit.Plan} (satisfied : NativeSourceInit.Satisfies plan state.mem)
    (covered : ∀ x ∈ ArmCert.Translate.Model.imageRowsPlan spec.imageRows, x ∈ plan)
    (declared : ArmCert.Translate.Model.PermissionRowsDeclared rows spec.imageRows)
    (coverage : ArmCert.Translate.Model.checkPermissionRowsCovered rows
      (ArmCert.Translate.Model.rowsFootprint spec.imageRows) = true)
    (pure : ArmCert.Translate.Model.checkImagePure spec.imageRows (spec.params.pie == 1#1)
      (spec.params.ha == 1#1) (spec.params.hd == 1#1) = true)
    (attributes : ArmCert.Translate.Model.checkAttributeImage spec.imageRows config = true)
    (writeback : ArmCert.Translate.Model.checkWriteBackAttributeImage spec.imageRows config = true)
    (other : ArmFull.Regs) (otherOff : ArmCertWalk.e0OverlayEnabled other = false)
    (off : ArmCertWalk.e0OverlayEnabled state.regs = false)
    (permissions : ArmCert.Translate.Model.checkPermissionImagePure rows (permissionParamsView spec.params)
      other spec.controls = true) :
    ArmCert.Translate.Model.CurrentImagesAt spec config rows state ∧
      ArmCertWalk.RawImageAt spec.imageRows state.mem := by
  have bytes : ArmCert.Translate.Model.checkImage spec.imageRows (spec.params.pie == 1#1)
      (spec.params.ha == 1#1) (spec.params.hd == 1#1) state.mem = true :=
    (ArmCert.Translate.Model.checkImage_of_satisfies satisfied covered).trans pure
  have perm : ArmCert.Translate.Model.checkPermissionImage rows spec.params state.regs spec.controls state.mem = true := by
    rw [ArmCert.Translate.Model.checkPermissionImage_of_satisfies satisfied covered declared,
      checkPermissionImagePure_view rows spec.params state.regs other spec.controls off otherOff]
    exact permissions
  exact ⟨ArmCert.Translate.Model.check_current_images_sound spec config rows state coverage bytes attributes
      writeback perm,
    ArmCertWalk.raw_image_of_check _ _ _ _ _ bytes⟩

#check "CURRENT_DECL GB10.noUpdateParamsView"
/-- The only walk-parameter fields the no-update check reads. -/
def noUpdateParamsView (p : ArmFull.S1TTWParams) : ArmFull.S1TTWParams :=
  { (default : ArmFull.S1TTWParams) with ha := p.ha, hd := p.hd, pie := p.pie, haft := p.haft }

/-- The only access fields the no-update check reads. -/
def noUpdateAccessView (write : Bool) : ArmFull.AccessDescriptor :=
  { (default : ArmFull.AccessDescriptor) with write := write, acctype := .AccessType_GPR }

theorem noUpdateRows_view (p : ArmFull.S1TTWParams) (acc : ArmFull.AccessDescriptor)
    (rows : List ArmCert.Translate.Model.ImageRow) (gpr : acc.acctype = .AccessType_GPR) :
    ArmCertWalk.NoUpdateRows p acc rows =
      ArmCertWalk.NoUpdateRows (noUpdateParamsView p) (noUpdateAccessView acc.write) rows := by
  unfold ArmCertWalk.NoUpdateRows
  apply ArmCert.Translate.Model.all_congr_mem
  intro row _
  simp only [ArmCertWalk.RowNoUpdate, ArmCertWalk.leafUpdateWord, ArmCertWalk.leafDirtyEnabled,
    S1TableUpdate.word, noUpdateParamsView, noUpdateAccessView, gpr]
  exact rfl

#check "CURRENT_DECL GB10.noUpd_of_view"
/-- Atom shape `∀ wr acc, DataShape wr acc → NoUpdateRows p acc rows = true` from two finite checks. -/
theorem noUpd_of_view (p : ArmFull.S1TTWParams) (rows : List ArmCert.Translate.Model.ImageRow)
    (checked : ∀ w : Bool, ArmCertWalk.NoUpdateRows (noUpdateParamsView p) (noUpdateAccessView w) rows = true) :
    ∀ (wr : Bool) (acc : ArmFull.AccessDescriptor), ArmCert.Translate.Model.DataShape wr acc →
      ArmCertWalk.NoUpdateRows p acc rows = true := by
  intro wr acc shape
  rw [noUpdateRows_view p acc rows shape.acctype]
  exact checked acc.write

#check "CURRENT_DECL GB10.checkPermissionImageNoOverlay"
/-- The permission-image check with no stage-1 overlay: no register file at all. -/
def checkPermissionImageNoOverlay (rows : List ArmCert.Translate.Model.PermissionRow) (p : ArmFull.S1TTWParams)
    (controls : S1LogicalReference.Controls) : Bool :=
  rows.all fun row => decide (row.slot % 8 = 0) &&
    (decide (ArmCert.Translate.Model.nativeAdmissionView p false row.witness =
        ArmCert.Translate.Model.el0AdmissionView p false
          (ArmCertWalk.descriptorPermissionView controls row.prior row.raw)) &&
      ArmCertWalk.permissionChecksPass row.witness p row.attributes row.access
        (ArmCertWalk.finishControls (ArmCertWalk.baseControls row.witness p) false (0#1, 0#1, 0#1)))

theorem checkPermissionImagePure_noOverlay (rows : List ArmCert.Translate.Model.PermissionRow)
    (p : ArmFull.S1TTWParams) (regs : ArmFull.Regs) (controls : S1LogicalReference.Controls)
    (off : ArmCertWalk.e0OverlayEnabled regs = false) :
    ArmCert.Translate.Model.checkPermissionImagePure rows p regs controls = checkPermissionImageNoOverlay rows p controls := by
  unfold ArmCert.Translate.Model.checkPermissionImagePure checkPermissionImageNoOverlay
  apply ArmCert.Translate.Model.all_congr_mem
  intro row _
  simp only [ArmCert.Translate.Model.PermissionRow.checkPure, ArmCert.Translate.Model.checkCanonicalAdmission,
    ArmCertWalk.computedControls, off, ArmCertWalk.finishControls, Bool.and_false, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte]

end ReleaseProfile.GB10

#print axioms ReleaseProfile.GB10.checkPermissionImagePure_view
#print axioms ReleaseProfile.GB10.e0Overlay_source
#print axioms ReleaseProfile.GB10.mair_source
#print axioms ReleaseProfile.GB10.attributeImage_source
#print axioms ReleaseProfile.GB10.writeBackImage_source
#print axioms ReleaseProfile.GB10.images_of_checks
#print axioms ReleaseProfile.GB10.noUpd_of_view
