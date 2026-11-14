import ArmCertWalk.E0POEnabledSource
import Pilot.ObservationSimp

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

namespace ArmCertWalk

def permissionSCR (registers : Regs) : BitVec 64 :=
  Mk_SCRType (if registers.FeatureImpl[4] = false ∧ registers.FeatureImpl[5] = false ∧
      registers.FeatureImpl[6] = false ∧ registers.FeatureImpl[7] = false then
    Sail.BitVec.zeroExtend (registers.bank_BitVec_32 .SCR) 64
    else registers.bank_BitVec_64 .SCR_EL3)

def permissionTCR2Enabled (registers : Regs) : Bool :=
  if registers.FeatureImpl[178] = false then false
  else if Sail.BitVec.extractLsb (registers.bank_BitVec_64 .SCR_EL3) 43 43 = 0#1 then false
  else if Sail.BitVec.extractLsb (permissionSCR registers) 0 0 = 1#1 then true
  else if registers.FeatureImpl[117] = true then
    Sail.BitVec.extractLsb (registers.bank_BitVec_64 .SCR_EL3) 18 18 == 1#1
  else false

/-- Pure current-register test, with feature support and enabled controls kept
distinct. No UNKNOWN feature is assigned false. -/
def e0OverlayEnabled (registers : Regs) : Bool :=
  if registers.FeatureImpl[210] = false then false
  else if permissionTCR2Enabled registers then
    Sail.BitVec.extractLsb (registers.bank_BitVec_64 .TCR2_EL2) 2 2 == 1#1
  else false

def PermissionQueryEffect (value : Bool) (state : State) :
    EStateM.Result (Sail.Error exception) State Bool → Prop
  | .ok answer other => answer = value ∧ other.regs = state.regs ∧
      other.mem = state.mem ∧ other.events = state.events
  | .error _ _ => False

theorem tcr2_permission_query_effect (state : State) :
    PermissionQueryEffect (permissionTCR2Enabled state.regs) state
      (IsTCR2EL2Enabled () state) := by
  rw [TCR2EnabledSource.complete]
  observe_simp [PermissionQueryEffect, permissionTCR2Enabled, permissionSCR,
    TCR2EnabledSource.native]
  simp only [Bool.beq_eq_decide_eq]

theorem e0_overlay_query_effect (nv1 : BitVec 1) (state : State) :
    PermissionQueryEffect (e0OverlayEnabled state.regs) state
      (AArch64_S1E0POEnabled .Regime_EL20 nv1 state) := by
  rw [E0POEnabledSource.complete]
  observe_simp [PermissionQueryEffect, e0OverlayEnabled, permissionTCR2Enabled,
    permissionSCR, E0POEnabledSource.native]

theorem e0_overlay_query_total (nv1 : BitVec 1) (state : State) :
    ∃ other, AArch64_S1E0POEnabled .Regime_EL20 nv1 state =
      .ok (e0OverlayEnabled state.regs) other ∧ other.regs = state.regs ∧
      other.mem = state.mem ∧ other.events = state.events := by
  have effect := e0_overlay_query_effect nv1 state
  cases actual : AArch64_S1E0POEnabled .Regime_EL20 nv1 state with
  | error err other => simp only [actual, PermissionQueryEffect] at effect
  | ok answer other =>
    have detail := by simpa only [actual, PermissionQueryEffect] using effect
    exact ⟨other, by rw [← detail.1], detail.2⟩

#print axioms tcr2_permission_query_effect
#print axioms e0_overlay_query_effect
#print axioms e0_overlay_query_total

end ArmCertWalk
