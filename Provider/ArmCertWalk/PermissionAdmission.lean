import ArmCertWalk.ComputedPermissionMeaning
import ArmCertWalk.AttributeMeaning

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

def overlayReadAllowed : Option OverlayRights → Bool
  | none => true
  | some rights => rights.1 == 1#1

def overlayWriteAllowed : Option OverlayRights → Bool
  | none => true
  | some rights => rights.2.1 == 1#1

def overlayExecuteAllowed : Option OverlayRights → Bool
  | none => true
  | some rights => rights.2.2 == 1#1

def normalAttributeKind : S1LogicalReference.AttributeKind → Bool
  | .normal _ _ => true
  | .device _ => false

/-- The source ordinary read/write branch includes GPR and SIMD accesses.
Cache-maintenance and GCS-specific operations have separate source policies. -/
def ordinaryPermissionKind (kind : AccessType) : Bool :=
  (kind != .AccessType_IFETCH) && (kind != .AccessType_DC) &&
    (kind != .AccessType_IC) && (kind != .AccessType_GCS)

/-- A finite, executable check of current descriptor/control/access data.
No native call, returned fault, oracle answer or future-success law is tested. -/
def permissionChecksPass (permissions : Permissions) (params : S1TTWParams)
    (attrs : AttributeBody) (input : AccessDescriptor) (controls : ComputedControlView) : Bool :=
  if input.acctype == .AccessType_IFETCH then
    normalAttributeKind attrs.kind && (controls.x == 1#1) &&
      overlayExecuteAllowed controls.overlay
  else ordinaryPermissionKind input.acctype &&
    ((!input.read) || ((controls.r == 1#1) && overlayReadAllowed controls.overlay)) &&
    ((!input.write) || ((controls.w == 1#1) && overlayWriteAllowed controls.overlay)) &&
    !(input.write && input.tagaccess && (attrs.tags == .MemTag_CanonicallyTagged)) &&
    !(input.write && !((params.ha +++ params.hd) == 3#2) &&
      (params.pie == 1#1) && (permissions.ndirty == 1#1))

def PermissionAdmissible (permissions : Permissions) (params : S1TTWParams)
    (attrs : AttributeBody) (input : AccessDescriptor) (controls : ComputedControlView) : Prop :=
  permissionChecksPass permissions params attrs input controls = true

end ArmCertWalk
