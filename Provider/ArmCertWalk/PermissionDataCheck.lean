import ArmCertWalk.PermissionCheckSource
import ArmCertWalk.PermissionDataGuards

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

namespace ArmCertWalk

theorem permission_data_body_eq (fault : FaultRecord) (ws : TTWState)
    (wp : S1TTWParams) (input : AccessDescriptor) (controls : S1AccessControls) (state : State)
    (notFetch : (input.acctype == .AccessType_IFETCH) = false)
    (admissible : PermissionAdmissible ws.permissions wp (attributeProjection ws.memattrs)
      input (computedControlProjection controls)) :
    PermissionCheckSource.body fault ws wp input controls state = .ok fault state := by
  have checks := admissible
  simp only [PermissionAdmissible, permissionChecksPass, notFetch, Bool.false_eq_true,
    ↓reduceIte, Bool.and_eq_true] at checks
  rcases checks with ⟨⟨⟨⟨kind, reads⟩, writes⟩, tag⟩, dirty⟩
  have kinds := kind
  simp only [ordinaryPermissionKind, Bool.and_eq_true, bne, Bool.not_eq_true'] at kinds
  have noDC := kinds.1.1.2
  have noIC := kinds.1.2
  have noGCS := kinds.2
  have readGuards := read_permission_guards input.read controls reads
  have writeGuards := write_permission_guards input.write controls writes
  have tagGuard : (input.write && input.tagaccess &&
      (ws.memattrs.tags == .MemTag_CanonicallyTagged)) = false := by
    simpa only [attributeProjection, Bool.not_eq_true'] using tag
  have dirtyGuard : (input.write && !((wp.ha +++ wp.hd) == 3#2) &&
      (wp.pie == 1#1) && (ws.permissions.ndirty == 1#1)) = false := by
    simpa only [Bool.not_eq_true'] using dirty
  obtain ⟨gcsAnswer, gcsCall⟩ : ∃ answer, HaveGCS () state = .ok answer state := ⟨_, rfl⟩
  simp only [PermissionCheckSource.body, DirectPermissionSource.el0Nonsecure,
    notFetch, noDC, noIC, noGCS, Bool.false_eq_true, ↓reduceIte, Bind.bind, EStateM.bind,
    gcsCall, Bool.and_false, Pure.pure, EStateM.pure, readGuards.1, readGuards.2,
    writeGuards.1, writeGuards.2, tagGuard, dirtyGuard]

#print axioms permission_data_body_eq

end ArmCertWalk
