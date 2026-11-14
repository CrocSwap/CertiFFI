import ArmCertWalk.POEnabledSource
import ArmCertWalk.PermissionQueries

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

namespace ArmCertWalk

def privilegedOverlayEnabled (registers : Regs) : Bool :=
  if registers.FeatureImpl[210] = false then false
  else if permissionTCR2Enabled registers then
    Sail.BitVec.extractLsb (registers.bank_BitVec_64 .TCR2_EL2) 3 3 == 1#1
  else false

def outputOverlayEnabled (registers : Regs) : Bool :=
  privilegedOverlayEnabled registers || e0OverlayEnabled registers

theorem privileged_overlay_query_effect (state : State) :
    PermissionQueryEffect (privilegedOverlayEnabled state.regs) state
      (AArch64_S1POEnabled .Regime_EL20 state) := by
  rw [POEnabledSource.complete]
  observe_simp [PermissionQueryEffect, privilegedOverlayEnabled, permissionTCR2Enabled,
    permissionSCR, POEnabledSource.native]

theorem privileged_overlay_query_total (state : State) :
    ∃ other, AArch64_S1POEnabled .Regime_EL20 state =
      .ok (privilegedOverlayEnabled state.regs) other ∧ other.regs = state.regs ∧
      other.mem = state.mem ∧ other.events = state.events := by
  have effect := privileged_overlay_query_effect state
  cases actual : AArch64_S1POEnabled .Regime_EL20 state with
  | error err other => simp only [actual, PermissionQueryEffect] at effect
  | ok answer other =>
    have detail := by simpa only [actual, PermissionQueryEffect] using effect
    exact ⟨other, by rw [← detail.1], detail.2⟩

#print axioms privileged_overlay_query_effect
#print axioms privileged_overlay_query_total

end ArmCertWalk
