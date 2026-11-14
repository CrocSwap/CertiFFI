import ArmCertTranslateModel.HostCurrentParams
import ArmCertTranslateModel.PathPermissionBinding

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- Five current image-control checks. Geometry is checked against the source
    NORMALIZED TxSZ separately. The old raw-six-field helper is reused with a
    temporary raw TxSZ; no raw range or raw=normalized condition is introduced. -/
def checkHostImageCore (regs : Regs) (params : S1TTWParams) : Bool :=
  decide (params.ha = hostHA regs) && decide (params.hd = hostHD regs) &&
  decide (params.pie = hostPIE regs) &&
  decide (params.wxn = _get_SCTLR_EL2_Type_WXN (regs.bank_BitVec_64 .SCTLR_EL2)) &&
  decide (params.mtx = (if regs.FeatureImpl[191] then Sail.BitVec.extractLsb (regs.bank_BitVec_64 .TCR_EL2) 60 60 else 0#1))

theorem check_host_image_core_sound (regs : Regs) (params : S1TTWParams)
    (checked : checkHostImageCore regs params = true) :
    HostImageParamsAt regs {params with txsz := _get_TCR_EL2_Type_T0SZ (regs.bank_BitVec_64 .TCR_EL2)} := by
  simp only [checkHostImageCore, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact ⟨checked.1.1.1.1, checked.1.1.1.2, checked.1.1.2, checked.1.2, checked.2, rfl⟩

/-- Parameter algebra for the actual source's TxSZ-only normalization. The
    normalized scalar will be the source-derived value, never an assumed range. -/
theorem image_params_eq_normalized_txsz (before after : S1TTWParams) (raw effective : BitVec 6)
    (actual : ImageParamsEq {before with txsz := raw} after)
    (geometry : before.txsz = effective) :
    ImageParamsEq before {after with txsz := effective} :=
  ⟨actual.ha, actual.hd, actual.pie, actual.wxn, actual.mtx, geometry⟩

/-- Static row-use data observes only HA/HD/PIE and the permission attribute
    key's MTX. In particular changing TxSZ does not require equal geometry. -/
def PathPermissionUse.reparam_active {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {query : AccessQuery}
    {level bits : Nat} {base : BitVec 48} {leafLevel logical : Nat}
    {physical : FullAddress} {view : S1DescriptorPIE.View 64}
    {path : S1LogicalReference.Path (logicalObserve spec.logicalRows)
      (effectiveBits spec.physicalConfig).toNat query.va level bits base
      (.leaf leafLevel logical physical view)} {prior : S1LogicalReference.TablePermissions}
    (binding : PathPermissionUse spec config rows query path prior)
    (actual : S1TTWParams) (ha : spec.params.ha = actual.ha) (hd : spec.params.hd = actual.hd)
    (pie : spec.params.pie = actual.pie) (mtx : spec.params.mtx = actual.mtx) :
    PathPermissionUse {spec with params := actual} config rows query path prior := by
  refine ⟨binding.row, binding.member, binding.slot, binding.words, binding.annotation,
    binding.used, ?_, ?_, binding.kind, binding.read, binding.write, binding.tagaccess⟩
  · simpa only [ha, hd, pie] using binding.rowView
  · simpa only [checkPermissionRowAttributes, mtx] using binding.attributes

/-- Derive the SAME actual raw getter result and current images from five
    scalar bindings, independently of the static geometry's effective TxSZ.
    No caller supplies a getter success equation or future preservation law. -/
theorem host_getter_image_core_total {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (state : State)
    (regime : HostRegimeAt state)
    (bound : HostImageParamsAt state.regs
      {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (state.regs.bank_BitVec_64 .TCR_EL2)})
    (controls : HostPermissionControlsAt state.regs spec.controls)
    (images : CurrentImagesAt spec config rows state) :
    ∃ params next,
      AArch64_S1TTWParamsEL20 .SS_NonSecure .VARange_LOWER state = .ok params next ∧
      S1Normality.Frame state next ∧
      HostLower.Shape (state.regs.bank_BitVec_64 .TCR_EL2) (state.regs.bank_BitVec_64 .MAIR_EL2) params ∧
      HostFlagShape state.regs params ∧ HostAdmissionShape state.regs params ∧ params.disch = 0#1 ∧
      ImageParamsEq {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (state.regs.bank_BitVec_64 .TCR_EL2)} params ∧
      CurrentImagesAt {spec with params := params} config rows next ∧
      LeafPermissionControls params (outputOverlayEnabled next.regs) spec.controls ∧
      spec.controls.hpd = (params.hpd == 1#1) := by
  let temporary := {spec with params :=
    {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (state.regs.bank_BitVec_64 .TCR_EL2)}}
  have temporaryImages : CurrentImagesAt temporary config rows state :=
    images.reparam temporary.params rfl rfl rfl rfl
  obtain ⟨params, next, call, frame, shape, flags, reads, disch, active, afterImages, leaf, hpd⟩ :=
    host_getter_current_images_total temporary config rows state regime bound controls temporaryImages
  exact ⟨params, next, call, frame, shape, flags, reads, disch, active, afterImages, leaf, hpd⟩

#print axioms check_host_image_core_sound
#print axioms image_params_eq_normalized_txsz
#print axioms PathPermissionUse.reparam_active
#print axioms host_getter_image_core_total
end ArmCert.Translate.Model
