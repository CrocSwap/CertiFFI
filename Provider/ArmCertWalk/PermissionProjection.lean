import ArmCertWalk.Profile
import Walk.S1LogicalDescriptor

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

def nativeTablePermissionProjection (permissions : ArmFull.Permissions) :
    S1LogicalReference.TablePermissions :=
  { ap := permissions.ap_table
    pxn := permissions.pxn_table.getLsbD 0
    uxn := permissions.uxn_table.getLsbD 0 }

/-- Active EL20 permission data only. Classic AP[0], XN-only regimes, S2 fields
and inactive PIE/classic/overlay values are not part of this projection. -/
def nativePermissionProjection (params : S1TTWParams) (overlayActive : Bool)
    (permissions : ArmFull.Permissions) : S1LogicalReference.Permissions :=
  { table := nativeTablePermissionProjection permissions
    leaf := if params.pie == 1#1 then
      .indirect ⟨permissions.ppi, permissions.upi, permissions.ndirty.getLsbD 0⟩
      else .classic ⟨permissions.ap.extractLsb' 1 2, permissions.pxn.getLsbD 0,
        some (permissions.uxn.getLsbD 0)⟩
    overlayIndex := if overlayActive then some permissions.po_index else none }

/-- The canonical pure leaf interpretation used by the actual source bridge.
The current table accumulator is data from the traversed Path. -/
def descriptorPermissionView (controls : S1LogicalReference.Controls)
    (prior : S1LogicalReference.TablePermissions) (descriptor : BitVec 64) :
    S1LogicalReference.Permissions :=
  S1LogicalReference.leafPermissions controls prior descriptor

end ArmCertWalk
