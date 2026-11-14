import ArmCertTranslateModel.PermissionInvariance
import ArmCertTranslateModel.StaticProjection

open Sail ArmFull ArmCertWalk
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

theorem allowed_dirty_bit_untracked (params : S1TTWParams) (role : DescriptorRole)
    (before after : BitVec 64) (allowed : AllowedUpdate params role before after)
    (untracked : params.ha +++ params.hd ≠ 3#2) : after.getLsbD 7 = before.getLsbD 7 := by
  obtain ⟨af, dirty, rfl, _, authorized⟩ := allowed
  cases dirty with
  | false =>
    cases af <;> simp only [S1Descriptor.hardwareUpdate, Bool.false_eq_true, ↓reduceIte]
    exact S1Descriptor.setAF_other before 7 (by decide)
  | true =>
    obtain ⟨_, ha, hd, _⟩ := authorized rfl
    exact False.elim (untracked (by rw [ha, hd]; decide))

/-- Preserve the canonical active admission data across the actual authorized
    hardware word relation. Tracked PIE notDirty is inactive and may change.
    Inherited table permissions are retained, not assumed zero. -/
theorem allowed_admission_permission_view (params : S1TTWParams) (role : DescriptorRole)
    (before after : BitVec 64) (allowed : AllowedUpdate params role before after)
    (controls : S1LogicalReference.Controls) (prior : S1LogicalReference.TablePermissions)
    (ha : controls.ha = (params.ha == 1#1)) (hd : controls.hd = (params.hd == 1#1))
    (pie : controls.pie = (params.pie == 1#1)) :
    admissionPermissionView params (descriptorPermissionView controls prior after) =
      admissionPermissionView params (descriptorPermissionView controls prior before) := by
  have overlay := (allowed_delta params role before after allowed).slice_eq 60 3
    (by decide) (by omega) (by omega)
  cases mode : controls.pie with
  | false =>
    have sourceMode : params.pie = 0#1 := pie_zero_of_false params (pie.symm.trans mode)
    have classic := allowed_classic_permissions params role before after allowed controls sourceMode ha hd
    simp only [descriptorPermissionView, S1LogicalReference.leafPermissions, mode,
      Bool.false_eq_true, ↓reduceIte, admissionPermissionView, classic, overlay]
  | true =>
    have index := allowed_permission_index params role before after allowed
    by_cases tracked : params.ha +++ params.hd = 3#2
    · simp only [descriptorPermissionView, S1LogicalReference.leafPermissions, mode,
        ↓reduceIte, admissionPermissionView, S1LogicalReference.indirectPermissions,
        index, tracked, overlay]
    · have dirty := allowed_dirty_bit_untracked params role before after allowed tracked
      simp only [descriptorPermissionView, S1LogicalReference.leafPermissions, mode,
        ↓reduceIte, admissionPermissionView, S1LogicalReference.indirectPermissions,
        index, tracked, dirty, overlay]

#print axioms allowed_dirty_bit_untracked
#print axioms allowed_admission_permission_view
end ArmCert.Translate.Model
