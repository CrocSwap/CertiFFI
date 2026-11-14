import ArmCertWalk.IndirectPermissionMeaning
import ArmCertWalk.OverlayPermissionFacts
import ArmCertWalk.PermissionQueries

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

structure ComputedControlView where
  r : BitVec 1
  w : BitVec 1
  x : BitVec 1
  gcs : BitVec 1
  overlay : Option OverlayRights
  wxn : BitVec 1
  deriving BEq, Repr

def computedControlProjection (controls : S1AccessControls) : ComputedControlView :=
  ⟨controls.r, controls.w, controls.x, controls.gcs,
    if controls.overlay then some (overlayProjection controls) else none, controls.wxn⟩

def baseControls (permissions : Permissions) (params : S1TTWParams) : BaseControlView :=
  if params.pie = 1#1 then indirectControls permissions else directControls permissions params

/-- Source WXN rules apply to the selected base and active overlay. -/
def finishControls (base : BaseControlView) (enabled : Bool) (overlay : OverlayRights) :
    ComputedControlView :=
  let active := base.overlay && enabled
  let overlayWriteInhibited := active && (base.wxn == 1#1) && (overlay.2.2 == 1#1)
  let x := if overlayWriteInhibited then base.x else if base.wxn == 1#1 then 0#1 else base.x
  let rights := if overlayWriteInhibited then (overlay.1, 0#1, overlay.2.2) else overlay
  ⟨base.r, base.w, x, base.gcs, if active then some rights else none, base.wxn⟩

def computedControls (permissions : Permissions) (params : S1TTWParams) (registers : Regs) :
    ComputedControlView :=
  finishControls (baseControls permissions params) (e0OverlayEnabled registers)
    (currentOverlayRights permissions registers)

end ArmCertWalk
