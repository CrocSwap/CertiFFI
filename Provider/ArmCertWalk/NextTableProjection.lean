import ArmCertWalk.NextTableFacts

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

theorem bit_zero_or_one (bit : BitVec 1) : bit = 0#1 ∨ bit = 1#1 := by
  have bound := bit.isLt
  simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat]
  omega

theorem source_table_base_eq (descriptor : BitVec 64) :
    sourceTableBase descriptor = S1LogicalReference.pageBase descriptor := by
  simp [sourceTableBase, S1LogicalReference.pageBase, Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange', Sail.BitVec.extractLsb, BitVec.extractLsb]

theorem next_table_permission_projection (params : S1TTWParams) (permissions : Permissions)
    (descriptor : BitVec 64) (controls : S1LogicalReference.Controls)
    (regime : controls.regime = .el20)
    (hpdBinding : controls.hpd = (params.hpd == 1#1))
    (pieBinding : controls.pie = (params.pie == 1#1)) :
    nativeTablePermissionProjection (nextTablePermissions params permissions descriptor) =
      S1LogicalReference.tablePermissions controls
        (nativeTablePermissionProjection permissions) descriptor := by
  rcases bit_zero_or_one params.hpd with hpd | hpd <;>
    rcases bit_zero_or_one params.pie with pie | pie
  all_goals simp only [hpd, pie, BitVec.reduceEq] at hpdBinding pieBinding
  · simp only [nextTablePermissions, hpd, pie, BitVec.reduceEq, Bool.true_and, ↓reduceIte]
    exact table_permission_projection permissions descriptor controls regime hpdBinding pieBinding
  · simp [nextTablePermissions, hpd, pie, S1LogicalReference.tablePermissions, pieBinding]
  · simp [nextTablePermissions, hpd, pie, S1LogicalReference.tablePermissions, hpdBinding]
  · simp [nextTablePermissions, hpd, pie, S1LogicalReference.tablePermissions, hpdBinding]

#print axioms source_table_base_eq
#print axioms next_table_permission_projection

end ArmCertWalk
