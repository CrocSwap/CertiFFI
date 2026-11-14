import ArmCertWalk.PermissionProjection
import ArmCertWalk.PermissionCheckTotal

open Sail ArmFull ArmCertWalk
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

/-- The checker does not inspect raw PIE dirty state when HA+HD repair is
    enabled. Erase only that inactive field, retaining the canonical data. -/
def admissionPermissionView (params : S1TTWParams) (view : S1LogicalReference.Permissions) :
    S1LogicalReference.Permissions :=
  {view with leaf := match view.leaf with
    | .classic c => .classic c
    | .indirect i => .indirect {i with notDirty := if params.ha +++ params.hd = 3#2 then false else i.notDirty}}

def nativeAdmissionView (params : S1TTWParams) (overlay : Bool) (permissions : ArmFull.Permissions) :=
  admissionPermissionView params (nativePermissionProjection params overlay permissions)

private theorem bit0_ext (a b : BitVec 1) (equal : a.getLsbD 0 = b.getLsbD 0) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i bound
  have zero : i = 0 := by omega
  subst i; exact equal

theorem base_controls_congr (params : S1TTWParams) (overlay : Bool) (left right : ArmFull.Permissions)
    (same : nativeAdmissionView params overlay left = nativeAdmissionView params overlay right) :
    baseControls left params = baseControls right params := by
  have tableAP : left.ap_table = right.ap_table :=
    congrArg (fun view : S1LogicalReference.Permissions => view.table.ap) same
  have tableUXN : left.uxn_table = right.uxn_table := bit0_ext _ _
    (congrArg (fun view : S1LogicalReference.Permissions => view.table.uxn) same)
  by_cases pie : params.pie = 1#1
  · have ppi : left.ppi = right.ppi := by
      have field := congrArg (fun view : S1LogicalReference.Permissions =>
        match view.leaf with | .indirect i => i.privileged | _ => 0#4) same
      simpa [nativeAdmissionView, admissionPermissionView, nativePermissionProjection, pie] using field
    have upi : left.upi = right.upi := by
      have field := congrArg (fun view : S1LogicalReference.Permissions =>
        match view.leaf with | .indirect i => i.unprivileged | _ => 0#4) same
      simpa [nativeAdmissionView, admissionPermissionView, nativePermissionProjection, pie] using field
    simp only [baseControls, pie, ↓reduceIte, indirectControls, indirectUserRights, ppi, upi]
    rw [upi]
  · have ap : left.ap.extractLsb' 1 2 = right.ap.extractLsb' 1 2 := by
      have field := congrArg (fun view : S1LogicalReference.Permissions =>
        match view.leaf with | .classic c => c.ap | _ => 0#2) same
      simpa [nativeAdmissionView, admissionPermissionView, nativePermissionProjection, pie] using field
    have uxnOption : some (left.uxn.getLsbD 0) = some (right.uxn.getLsbD 0) := by
      have field := congrArg (fun view : S1LogicalReference.Permissions =>
        match view.leaf with | .classic c => c.uxn | _ => none) same
      simpa [nativeAdmissionView, admissionPermissionView, nativePermissionProjection, pie] using field
    have uxn := bit0_ext left.uxn right.uxn (Option.some.inj uxnOption)
    have selector : Sail.BitVec.extractLsb left.ap 2 1 = Sail.BitVec.extractLsb right.ap 2 1 := ap
    simp only [baseControls, pie, ↓reduceIte, directControls, directTableRights, directLeafRights,
      tableAP, tableUXN, selector, uxn]

theorem computed_controls_congr (params : S1TTWParams) (regs : Regs) (left right : ArmFull.Permissions)
    (same : nativeAdmissionView params (e0OverlayEnabled regs) left =
      nativeAdmissionView params (e0OverlayEnabled regs) right) :
    computedControls left params regs = computedControls right params regs := by
  have base := base_controls_congr params _ left right same
  unfold computedControls
  rw [base]
  cases enabled : e0OverlayEnabled regs with
  | false => simp [finishControls]
  | true =>
    have index : left.po_index = right.po_index := by
      have field := congrArg (fun view : S1LogicalReference.Permissions => view.overlayIndex) same
      simpa [nativeAdmissionView, admissionPermissionView, nativePermissionProjection, enabled] using field
    simp only [currentOverlayRights, index]

theorem admission_ndirty_congr (params : S1TTWParams) (overlay : Bool) (left right : ArmFull.Permissions)
    (same : nativeAdmissionView params overlay left = nativeAdmissionView params overlay right)
    (pie : params.pie = 1#1) (untracked : params.ha +++ params.hd ≠ 3#2) :
    left.ndirty = right.ndirty := by
  apply bit0_ext
  have field := congrArg (fun view : S1LogicalReference.Permissions =>
    match view.leaf with | .indirect i => i.notDirty | _ => false) same
  simpa [nativeAdmissionView, admissionPermissionView, nativePermissionProjection, pie, untracked] using field

/-- Representation independence for the complete pure native checker policy.
    Inactive fields, including tracked PIE dirty state, are not fixed. -/
theorem permission_admissible_congr (params : S1TTWParams) (regs : Regs)
    (left right : ArmFull.Permissions) (attrs : AttributeBody) (input : AccessDescriptor)
    (same : nativeAdmissionView params (e0OverlayEnabled regs) left =
      nativeAdmissionView params (e0OverlayEnabled regs) right) :
    PermissionAdmissible left params attrs input (computedControls left params regs) ↔
      PermissionAdmissible right params attrs input (computedControls right params regs) := by
  have computed := computed_controls_congr params regs left right same
  unfold PermissionAdmissible permissionChecksPass
  rw [computed]
  by_cases tracked : params.ha +++ params.hd = 3#2
  · simp [tracked]
  · by_cases pie : params.pie = 1#1
    · rw [admission_ndirty_congr params _ left right same pie tracked]
    · simp [pie]

#print axioms base_controls_congr
#print axioms computed_controls_congr
#print axioms admission_ndirty_congr
#print axioms permission_admissible_congr
end ArmCert.Translate.Model
