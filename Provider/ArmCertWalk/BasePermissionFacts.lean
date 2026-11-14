import ArmCertWalk.ComputedPermissionMeaning
import ArmCertWalk.DirectPermissionTotal
import ArmCertWalk.IndirectPermissionTotal

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

def basePermissionCall (ws : TTWState) (wp : S1TTWParams) (input : AccessDescriptor) :
    SailM S1AccessControls :=
  if wp.pie == 1#1 then AArch64_S1IndirectBasePermissions .Regime_EL20 ws wp input
  else AArch64_S1DirectBasePermissions .Regime_EL20 ws wp input

theorem base_permissions_total (ws : TTWState) (wp : S1TTWParams)
    (input : AccessDescriptor) (state : State) (el : input.el = EL0)
    (security : input.ss = .SS_NonSecure) :
    ∃ controls other, basePermissionCall ws wp input state = .ok controls other ∧
      baseControlProjection controls = baseControls ws.permissions wp ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  by_cases pie : wp.pie = 1#1
  · simpa only [basePermissionCall, baseControls, beq_iff_eq, pie, ↓reduceIte] using
      indirect_permissions_total ws wp input state el security
  · simpa only [basePermissionCall, baseControls, beq_iff_eq, pie, ↓reduceIte] using
      direct_permissions_total ws wp input state el security

#print axioms base_permissions_total

end ArmCertWalk
