import ArmCertWalk.PermissionBitFacts
import ArmCertWalk.PermissionAPFacts

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

namespace ArmCertWalk

/-- Equalities only for the active inputs of the EL20 leaf permission source.
PIR words are constrained only in the PIE branch. Other control fields remain
free. The current-getter/root binding must derive this record. -/
structure LeafPermissionControls (params : S1TTWParams) (overlay : Bool)
    (controls : S1LogicalReference.Controls) : Prop where
  regime : controls.regime = .el20
  pie : controls.pie = (params.pie == 1#1)
  ha : controls.ha = (params.ha == 1#1)
  hd : controls.hd = (params.hd == 1#1)
  pir : params.pie = 1#1 → controls.pir = params.pir
  pire0 : params.pie = 1#1 → controls.pire0 = params.pire0
  overlayEnabled : (controls.poe || controls.e0poe) = overlay

theorem output_permission_projection (permissions : Permissions) (descriptor : BitVec 64)
    (params : S1TTWParams) (overlay : Bool) (controls : S1LogicalReference.Controls)
    (binding : LeafPermissionControls params overlay controls) :
    nativePermissionProjection params overlay
      (outputPermissionValue permissions descriptor params overlay) =
      descriptorPermissionView controls (nativeTablePermissionProjection permissions) descriptor := by
  have regimes : (S1LogicalReference.Regime.el20 == S1LogicalReference.Regime.el10) = false := by decide
  cases overlay <;> by_cases pie : params.pie = 1#1 <;>
    by_cases ha : params.ha = 1#1 <;> by_cases hd : params.hd = 1#1 <;>
    cases dbm : descriptor.getLsbD 51
  all_goals simp [nativePermissionProjection, nativeTablePermissionProjection,
    outputPermissionValue, descriptorPermissionView, S1LogicalReference.leafPermissions,
    S1LogicalReference.indirectPermissions, S1LogicalReference.classicPermissions,
    S1LogicalReference.nv1Mode, binding.regime, binding.pie, binding.ha, binding.hd,
    binding.pir, binding.pire0, binding.overlayEnabled, pie, ha, hd, dbm, regimes,
    ← BitVec.getLsbD_eq_getElem, Sail.BitVec.extractLsb, BitVec.extractLsb,
    sourcePermissionNibble_eq, source_permission_index, permission_nibble_shift,
    source_permission_bit_unextended descriptor 7 (by decide),
    source_permission_bit_unextended descriptor 51 (by decide),
    source_permission_bit_unextended descriptor 53 (by decide),
    source_permission_bit_unextended descriptor 54 (by decide),
    permission_overlay_index, permission_ap_extract, permission_ap_dirty]
  all_goals exact permission_overlay_index descriptor

#print axioms output_permission_projection

end ArmCertWalk
