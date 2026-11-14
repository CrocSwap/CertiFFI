import ArmCertWalk.DirectPermissionStages
import ArmCertWalk.PermissionMeaning
import Pilot.ObservationSimp

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

namespace ArmCertWalk

def DirectPermissionEffect (ws : TTWState) (wp : S1TTWParams) (state : State) :
    EStateM.Result (Sail.Error exception) State S1AccessControls → Prop
  | .ok controls other => baseControlProjection controls = directControls ws.permissions wp ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events
  | .error _ _ => False

theorem direct_permission_body_effect (ws : TTWState) (wp : S1TTWParams)
    (input : AccessDescriptor) (seed : DirectPermissionStages.StageAcc) (state : State) :
    DirectPermissionEffect ws wp state (DirectPermissionStages.body ws wp input seed state) := by
  rw [DirectPermissionStages.complete]
  observe_simp [DirectPermissionEffect, baseControlProjection, directControls,
    directLeafRights, directTableRights, DirectPermissionSource.el0Nonsecure,
    DirectPermissionStages.native]
  all_goals
    have cases2 (value : BitVec 2) :
        value = 0#2 ∨ value = 1#2 ∨ value = 2#2 ∨ value = 3#2 := by
      have bound := value.isLt
      simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat]
      omega
    rcases cases2 (Sail.BitVec.extractLsb ws.permissions.ap 2 1) with
      ap | ap | ap | ap <;>
      rcases cases2 ws.permissions.ap_table with table | table | table | table <;>
      simp [ap, table, EL0]

#print axioms direct_permission_body_effect

end ArmCertWalk
