import ArmCertWalk.OverlayEnable
import ArmCertWalk.PermissionProjection
import ArmCertWalk.PermissionWindows

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

def sourcePermissionIndex (descriptor : BitVec 64) : BitVec 4 :=
  ((Sail.BitVec.extractLsb descriptor 54 53 +++
    BitVec.setWidth 1 (BitVec.join1 [BitVec.access descriptor 51])) +++
    BitVec.setWidth 1 (BitVec.join1 [BitVec.access descriptor 6]))

/-- Pure value of the actual source updates. Inactive fields retain their
actual input values; only the active projection has a canonical meaning. -/
def outputPermissionValue (permissions : Permissions) (descriptor : BitVec 64)
    (params : S1TTWParams) (overlay : Bool) : Permissions :=
  let updated := if params.pie == 1#1 then
    { permissions with
      ppi := sourcePermissionNibble params.pir (sourcePermissionIndex descriptor)
      upi := sourcePermissionNibble params.pire0 (sourcePermissionIndex descriptor)
      ndirty := BitVec.setWidth 1 (BitVec.join1 [BitVec.access descriptor 7]) }
    else
      let classic := { permissions with
        ap := Sail.BitVec.updateSubrange permissions.ap 2 1 (Sail.BitVec.extractLsb descriptor 7 6)
        uxn := BitVec.setWidth 1 (BitVec.join1 [BitVec.access descriptor 54])
        pxn := BitVec.setWidth 1 (BitVec.join1 [BitVec.access descriptor 53]) }
      if params.ha == 1#1 && params.hd == 1#1 &&
          (BitVec.setWidth 1 (BitVec.join1 [BitVec.access descriptor 51]) == 1#1) then
        { classic with ap := BitVec.update classic.ap 2 (Bit 0#1) }
      else classic
  if overlay then
    { updated with po_index := 0#1 +++ Sail.BitVec.extractLsb descriptor 62 60 }
  else updated

end ArmCertWalk
