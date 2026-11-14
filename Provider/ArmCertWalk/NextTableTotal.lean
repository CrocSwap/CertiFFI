import ArmCertWalk.NextTableProjection

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

theorem next_table_canonical_total (params : S1TTWParams) (current : TTWState)
    (descriptor : BitVec 64) (s2fs1mro : Bool) (state : State)
    (controls : S1LogicalReference.Controls)
    (d128 : params.d128 = 0#1) (ds : params.ds = 0#1) (tg : params.tgx = .TGx_4KB)
    (nonsecure : current.baseaddress.paspace = .PAS_NonSecure)
    (regime : controls.regime = .el20)
    (hpdBinding : controls.hpd = (params.hpd == 1#1))
    (pieBinding : controls.pie = (params.pie == 1#1)) :
    ∃ next other,
      AArch64_S1NextWalkStateTable current s2fs1mro .Regime_EL20 params descriptor state =
        .ok next other ∧ NextTableMeaning params current descriptor next ∧
      next.baseaddress.address = S1LogicalReference.pageBase descriptor ∧
      nativeTablePermissionProjection next.permissions =
        S1LogicalReference.tablePermissions controls
          (nativeTablePermissionProjection current.permissions) descriptor ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  obtain ⟨next, other, call, meaning, registers, memory, events⟩ :=
    next_table_total params current descriptor s2fs1mro state d128 ds tg nonsecure
  refine ⟨next, other, call, meaning, ?_, ?_, registers, memory, events⟩
  · exact meaning.2.2.1.trans (source_table_base_eq descriptor)
  · rw [meaning.2.2.2.2.2.2.2]
    exact next_table_permission_projection params current.permissions descriptor controls
      regime hpdBinding pieBinding

#print axioms next_table_canonical_total

end ArmCertWalk
