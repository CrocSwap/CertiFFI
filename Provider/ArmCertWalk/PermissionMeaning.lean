import ArmCertWalk.Profile

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

/-- Base permission computation has not filled the separate overlay rights. -/
structure BaseControlView where
  r : BitVec 1
  w : BitVec 1
  x : BitVec 1
  gcs : BitVec 1
  overlay : Bool
  wxn : BitVec 1
  deriving BEq, Repr

def baseControlProjection (controls : S1AccessControls) : BaseControlView :=
  ⟨controls.r, controls.w, controls.x, controls.gcs, controls.overlay, controls.wxn⟩

abbrev DirectRights := BitVec 1 × BitVec 1 × BitVec 1 × BitVec 1

def directLeafRights (permissions : Permissions) : DirectRights :=
  let selector := Sail.BitVec.extractLsb permissions.ap 2 1
  if selector = 0#2 then (1#1, 1#1, 0#1, 0#1)
  else if selector = 1#2 then (1#1, 1#1, 1#1, 1#1)
  else if selector = 2#2 then (1#1, 0#1, 0#1, 0#1)
  else (1#1, 0#1, 1#1, 0#1)

def directTableRights (table : BitVec 2) (rights : DirectRights) : DirectRights :=
  if table = 0#2 then rights
  else if table = 1#2 then (rights.1, rights.2.1, 0#1, 0#1)
  else if table = 2#2 then (rights.1, 0#1, rights.2.2.1, 0#1)
  else (rights.1, 0#1, 0#1, 0#1)

/-- Pure current EL0/nonsecure direct-permission meaning, including inherited
AP/UXN restrictions and WXN. PAN support is not a parameter or assumption. -/
def directControls (permissions : Permissions) (params : S1TTWParams) : BaseControlView :=
  let rights := directTableRights permissions.ap_table (directLeafRights permissions)
  let x := ~~~(permissions.uxn ||| permissions.uxn_table)
  ⟨rights.2.2.1, rights.2.2.2, x, 0#1, true,
    params.wxn &&& rights.2.2.2 &&& x⟩

end ArmCertWalk
