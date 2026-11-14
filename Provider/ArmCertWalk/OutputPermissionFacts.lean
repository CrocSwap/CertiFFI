import ArmCertWalk.OutputPermissionSource
import ArmCertWalk.OutputPermissionMeaning

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

namespace ArmCertWalk

def OutputPermissionEffect (expected : Permissions) (state : State) :
    EStateM.Result (Sail.Error exception) State Permissions → Prop
  | .ok actual other => actual = expected ∧ other.regs = state.regs ∧
      other.mem = state.mem ∧ other.events = state.events
  | .error _ _ => False

theorem output_permission_effect (permissions : Permissions) (descriptor : BitVec 64)
    (params : S1TTWParams) (state : State) (d128 : params.d128 = 0#1) :
    OutputPermissionEffect
      (outputPermissionValue permissions descriptor params (outputOverlayEnabled state.regs)) state
      (AArch64_S1ApplyOutputPerms permissions descriptor .Regime_EL20 params state) := by
  rw [OutputPermissionSource.complete permissions descriptor params state d128]
  by_cases pie : params.pie = 1#1 <;>
    by_cases ha : params.ha = 1#1 <;>
    by_cases hd : params.hd = 1#1 <;>
    by_cases dbm : BitVec.join1 [BitVec.access descriptor 51] = 1#1
  all_goals observe_simp [OutputPermissionEffect, outputPermissionValue, sourcePermissionIndex,
    sourcePermissionNibble, outputOverlayEnabled, privilegedOverlayEnabled,
    e0OverlayEnabled, permissionTCR2Enabled, permissionSCR, OutputPermissionSource.native]
  all_goals simp_all [sourcePermissionNibble, sourcePermissionIndex]
  all_goals rfl

theorem output_permission_total (permissions : Permissions) (descriptor : BitVec 64)
    (params : S1TTWParams) (state : State) (d128 : params.d128 = 0#1) :
    ∃ other, AArch64_S1ApplyOutputPerms permissions descriptor .Regime_EL20 params state =
      .ok (outputPermissionValue permissions descriptor params
        (outputOverlayEnabled state.regs)) other ∧ other.regs = state.regs ∧
      other.mem = state.mem ∧ other.events = state.events := by
  have effect := output_permission_effect permissions descriptor params state d128
  cases actual : AArch64_S1ApplyOutputPerms permissions descriptor .Regime_EL20 params state with
  | error err other => simp only [actual, OutputPermissionEffect] at effect
  | ok answer other =>
    have detail := by simpa only [actual, OutputPermissionEffect] using effect
    exact ⟨other, by rw [← detail.1], detail.2⟩

#print axioms output_permission_effect
#print axioms output_permission_total

end ArmCertWalk
