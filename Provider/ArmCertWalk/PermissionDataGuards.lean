import ArmCertWalk.PermissionAdmission

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

namespace ArmCertWalk

theorem read_permission_guards (read : Bool) (controls : S1AccessControls)
    (allowed : ((!read) || ((controls.r == 1#1) &&
      overlayReadAllowed (computedControlProjection controls).overlay)) = true) :
    (read && controls.overlay && (controls.or == 0#1)) = false ∧
      (read && (controls.r == 0#1)) = false := by
  cases reading : read <;> cases active : controls.overlay <;>
    simp_all [computedControlProjection, overlayReadAllowed, overlayProjection]

theorem write_permission_guards (write : Bool) (controls : S1AccessControls)
    (allowed : ((!write) || ((controls.w == 1#1) &&
      overlayWriteAllowed (computedControlProjection controls).overlay)) = true) :
    (write && controls.overlay && (controls.ow == 0#1)) = false ∧
      (write && (controls.w == 0#1)) = false := by
  cases writing : write <;> cases active : controls.overlay <;>
    simp_all [computedControlProjection, overlayWriteAllowed, overlayProjection]

#print axioms read_permission_guards
#print axioms write_permission_guards

end ArmCertWalk
