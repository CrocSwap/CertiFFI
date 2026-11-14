import ArmCertWalk.TablePermissionSource
import ArmCertWalk.PermissionBitFacts

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

namespace ArmCertWalk

def tablePermissionValue (permissions : Permissions) (descriptor : BitVec 64) : Permissions :=
  { permissions with
    ap_table := permissions.ap_table ||| Sail.BitVec.extractLsb descriptor 62 61
    pxn_table := permissions.pxn_table |||
      BitVec.setWidth 1 (BitVec.join1 [BitVec.access descriptor 59])
    uxn_table := permissions.uxn_table |||
      BitVec.setWidth 1 (BitVec.join1 [BitVec.access descriptor 60]) }

def TablePermissionEffect (expected : Permissions) (state : State) :
    EStateM.Result (Sail.Error exception) State Permissions → Prop
  | .ok actual other => actual = expected ∧ other.regs = state.regs ∧
      other.mem = state.mem ∧ other.events = state.events
  | .error _ _ => False

theorem table_permission_effect (permissions : Permissions) (descriptor : BitVec 64)
    (params : S1TTWParams) (state : State) (d128 : params.d128 = 0#1) :
    TablePermissionEffect (tablePermissionValue permissions descriptor) state
      (AArch64_S1ApplyTablePerms permissions descriptor .Regime_EL20 params state) := by
  rw [TablePermissionSource.complete permissions descriptor params state d128]
  observe_simp [TablePermissionEffect, tablePermissionValue, TablePermissionSource.native]

theorem table_permission_total (permissions : Permissions) (descriptor : BitVec 64)
    (params : S1TTWParams) (state : State) (d128 : params.d128 = 0#1) :
    ∃ other, AArch64_S1ApplyTablePerms permissions descriptor .Regime_EL20 params state =
      .ok (tablePermissionValue permissions descriptor) other ∧ other.regs = state.regs ∧
      other.mem = state.mem ∧ other.events = state.events := by
  have effect := table_permission_effect permissions descriptor params state d128
  cases actual : AArch64_S1ApplyTablePerms permissions descriptor .Regime_EL20 params state with
  | error err other => simp only [actual, TablePermissionEffect] at effect
  | ok answer other =>
    have detail := by simpa only [actual, TablePermissionEffect] using effect
    exact ⟨other, by rw [← detail.1], detail.2⟩

theorem table_permission_projection (permissions : Permissions) (descriptor : BitVec 64)
    (controls : S1LogicalReference.Controls) (regime : controls.regime = .el20)
    (hpd : controls.hpd = false) (pie : controls.pie = false) :
    nativeTablePermissionProjection (tablePermissionValue permissions descriptor) =
      S1LogicalReference.tablePermissions controls
        (nativeTablePermissionProjection permissions) descriptor := by
  have regimes : (S1LogicalReference.Regime.el20 == S1LogicalReference.Regime.el10) = false := by decide
  simp [nativeTablePermissionProjection, tablePermissionValue,
    S1LogicalReference.tablePermissions, S1LogicalReference.nv1Mode, regime, hpd, pie, regimes,
    source_permission_bit_unextended descriptor 59 (by decide),
    source_permission_bit_unextended descriptor 60 (by decide)]
  rfl

#print axioms table_permission_effect
#print axioms table_permission_total
#print axioms table_permission_projection

end ArmCertWalk
