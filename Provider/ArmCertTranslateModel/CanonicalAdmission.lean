import ArmCertTranslateModel.PermissionPreservation
import ArmCertWalk.OutputPermissionTotal

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

/-- EL0 checks do not inspect privileged-only overlay indices. Keep the
    source-checked canonical data and erase only that inactive projection. -/
def el0AdmissionView (params : S1TTWParams) (enabled : Bool) (view : S1LogicalReference.Permissions) :
    S1LogicalReference.Permissions :=
  let active := admissionPermissionView params view
  {active with overlayIndex := if enabled then active.overlayIndex else none}

theorem native_admission_from_output (params : S1TTWParams) (regs : Regs) (raw : ArmFull.Permissions) :
    nativeAdmissionView params (e0OverlayEnabled regs) raw =
      el0AdmissionView params (e0OverlayEnabled regs)
        (nativePermissionProjection params (outputOverlayEnabled regs) raw) := by
  cases user : e0OverlayEnabled regs <;> cases privileged : privilegedOverlayEnabled regs <;>
    simp [nativeAdmissionView, el0AdmissionView, admissionPermissionView,
      nativePermissionProjection, outputOverlayEnabled, user, privileged]

/-- A current finite-data policy on the canonical projection. Quantification
    is over the native permission DATA representation, not over future states,
    source calls, faults, oracle outcomes or invariant-preservation answers. -/
def CanonicalAdmission (params : S1TTWParams) (regs : Regs)
    (view : S1LogicalReference.Permissions) (attrs : AttributeBody) (input : AccessDescriptor) : Prop :=
  ∀ raw : ArmFull.Permissions,
    nativeAdmissionView params (e0OverlayEnabled regs) raw =
      el0AdmissionView params (e0OverlayEnabled regs) view →
    PermissionAdmissible raw params attrs input (computedControls raw params regs)

/-- The witness is data used by the checker. Its inactive fields are never
    equated to the actual source result or pinned in the environment. -/
def checkCanonicalAdmission (params : S1TTWParams) (regs : Regs)
    (view : S1LogicalReference.Permissions) (attrs : AttributeBody) (input : AccessDescriptor)
    (witness : ArmFull.Permissions) : Bool :=
  decide (nativeAdmissionView params (e0OverlayEnabled regs) witness =
    el0AdmissionView params (e0OverlayEnabled regs) view) &&
  permissionChecksPass witness params attrs input (computedControls witness params regs)

theorem check_canonical_admission_sound (params : S1TTWParams) (regs : Regs)
    (view : S1LogicalReference.Permissions) (attrs : AttributeBody) (input : AccessDescriptor)
    (witness : ArmFull.Permissions)
    (checked : checkCanonicalAdmission params regs view attrs input witness = true) :
    CanonicalAdmission params regs view attrs input := by
  simp only [checkCanonicalAdmission, Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨keyEq, passes⟩ := checked
  intro raw same
  apply (permission_admissible_congr params regs raw witness attrs input (same.trans keyEq.symm)).mpr
  exact passes

theorem canonical_admission_congr (params : S1TTWParams) (regs : Regs)
    (first second : S1LogicalReference.Permissions) (attrs : AttributeBody) (input : AccessDescriptor)
    (same : admissionPermissionView params first = admissionPermissionView params second) :
    CanonicalAdmission params regs first attrs input ↔ CanonicalAdmission params regs second attrs input := by
  unfold CanonicalAdmission el0AdmissionView
  rw [same]

theorem canonical_admission_allowed_update (params : S1TTWParams) (regs : Regs)
    (role : DescriptorRole) (before after : BitVec 64) (allowed : AllowedUpdate params role before after)
    (controls : S1LogicalReference.Controls) (prior : S1LogicalReference.TablePermissions)
    (ha : controls.ha = (params.ha == 1#1)) (hd : controls.hd = (params.hd == 1#1))
    (pie : controls.pie = (params.pie == 1#1)) (attrs : AttributeBody) (input : AccessDescriptor) :
    CanonicalAdmission params regs (descriptorPermissionView controls prior after) attrs input ↔
      CanonicalAdmission params regs (descriptorPermissionView controls prior before) attrs input :=
  canonical_admission_congr params regs _ _ attrs input
    (allowed_admission_permission_view params role before after allowed controls prior ha hd pie)

/-- Actual native checker success and same-state frame derived from the
    canonical data certificate and the actual permission projection equation.
    The source output/table bridge produces that equation internally. -/
theorem canonical_permission_check_total (fault : FaultRecord) (ws : TTWState) (params : S1TTWParams)
    (input : AccessDescriptor) (state : State) (el : input.el = EL0) (security : input.ss = .SS_NonSecure)
    (view : S1LogicalReference.Permissions)
    (projection : nativePermissionProjection params (outputOverlayEnabled state.regs) ws.permissions = view)
    (admitted : CanonicalAdmission params state.regs view (attributeProjection ws.memattrs) input) :
    ∃ next, AArch64_S1CheckPermissions fault .Regime_EL20 ws params input state = .ok fault next ∧
      next.regs = state.regs ∧ next.mem = state.mem ∧ next.events = state.events := by
  apply permission_check_total fault ws params input state el security
  apply admitted ws.permissions
  rw [native_admission_from_output, projection]

#print axioms native_admission_from_output
#print axioms check_canonical_admission_sound
#print axioms canonical_admission_allowed_update
#print axioms canonical_permission_check_total
end ArmCert.Translate.Model
