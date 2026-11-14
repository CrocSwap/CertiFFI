import ArmCertWalk.OutputPermissionFacts
import ArmCertWalk.OutputPermissionProjection

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

theorem output_permissions_canonical_total (permissions : Permissions) (descriptor : BitVec 64)
    (params : S1TTWParams) (controls : S1LogicalReference.Controls) (state : State)
    (d128 : params.d128 = 0#1)
    (current : LeafPermissionControls params (outputOverlayEnabled state.regs) controls) :
    ∃ result other,
      AArch64_S1ApplyOutputPerms permissions descriptor .Regime_EL20 params state =
        .ok result other ∧
      nativePermissionProjection params (outputOverlayEnabled state.regs) result =
        descriptorPermissionView controls (nativeTablePermissionProjection permissions) descriptor ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  obtain ⟨other, call, registers, memory, events⟩ :=
    output_permission_total permissions descriptor params state d128
  exact ⟨_, other, call, output_permission_projection permissions descriptor params _ controls current,
    registers, memory, events⟩

#print axioms output_permissions_canonical_total

end ArmCertWalk
