import ArmCertWalk.PermissionCheckSource
import ArmCertWalk.PermissionAdmission

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

namespace ArmCertWalk

theorem permission_fetch_body_eq (fault : FaultRecord) (ws : TTWState)
    (wp : S1TTWParams) (input : AccessDescriptor) (controls : S1AccessControls) (state : State)
    (fetch : (input.acctype == .AccessType_IFETCH) = true)
    (admissible : PermissionAdmissible ws.permissions wp (attributeProjection ws.memattrs)
      input (computedControlProjection controls)) :
    PermissionCheckSource.body fault ws wp input controls state = .ok fault state := by
  have normalNotDevice : (MemType.MemType_Normal == .MemType_Device) = false := by decide
  cases overlay : controls.overlay with
  | false =>
    cases memory : ws.memattrs.memtype with
    | MemType_Device =>
      simp [PermissionAdmissible, permissionChecksPass, fetch, computedControlProjection,
        attributeProjection, memory, normalAttributeKind, overlayExecuteAllowed, overlay] at admissible
    | MemType_Normal =>
      have execute : controls.x = 1#1 := by
        simpa [PermissionAdmissible, permissionChecksPass, fetch, computedControlProjection,
          attributeProjection, memory, normalAttributeKind, overlayExecuteAllowed, overlay] using admissible
      simp [PermissionCheckSource.body, DirectPermissionSource.el0Nonsecure, fetch, memory,
        normalNotDevice, overlay, execute, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  | true =>
    cases memory : ws.memattrs.memtype with
    | MemType_Device =>
      simp [PermissionAdmissible, permissionChecksPass, fetch, computedControlProjection,
        attributeProjection, memory, normalAttributeKind, overlayExecuteAllowed, overlay] at admissible
    | MemType_Normal =>
      have rights : controls.x = 1#1 ∧ controls.ox = 1#1 := by
        simpa [PermissionAdmissible, permissionChecksPass, fetch, computedControlProjection,
          attributeProjection, memory, normalAttributeKind, overlayExecuteAllowed, overlay,
          overlayProjection] using admissible
      simp [PermissionCheckSource.body, DirectPermissionSource.el0Nonsecure, fetch, memory,
        normalNotDevice, overlay, rights.1, rights.2, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

#print axioms permission_fetch_body_eq

end ArmCertWalk
