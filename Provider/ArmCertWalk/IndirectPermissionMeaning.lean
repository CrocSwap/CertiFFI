import ArmCertWalk.IndirectPermissionTables

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

/-- The source rejects privileged execute/GCS together with user write/GCS. -/
def indirectConflict (privileged user : DirectRights) : Bool :=
  ((privileged.2.2.2 == 1#1) || (privileged.1 == 1#1)) &&
    ((user.2.2.1 == 1#1) || (user.1 == 1#1))

def indirectUserRights (permissions : Permissions) : DirectRights :=
  let privileged := indirectRights permissions.ppi
  let user := indirectRights permissions.upi
  if indirectConflict privileged user then (0#1, 0#1, 0#1, 0#1) else user

def indirectControls (permissions : Permissions) : BaseControlView :=
  let user := indirectUserRights permissions
  ⟨user.2.1, user.2.2.1, user.2.2.2, user.1,
    (~~~(BitVec.setWidth 1 (BitVec.join1 [BitVec.access permissions.upi 3]))) == 1#1,
    if permissions.upi == 6#4 then 1#1 else 0#1⟩

end ArmCertWalk
