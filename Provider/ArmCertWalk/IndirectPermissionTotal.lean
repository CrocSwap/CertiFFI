import ArmCertWalk.IndirectPermissionFacts
import ArmCertWalk.DirectPermissionTotal

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

theorem indirect_permissions_total (ws : TTWState) (wp : S1TTWParams)
    (input : AccessDescriptor) (state : State) (el : input.el = EL0)
    (security : input.ss = .SS_NonSecure) :
    ∃ controls other,
      AArch64_S1IndirectBasePermissions .Regime_EL20 ws wp input state = .ok controls other ∧
      baseControlProjection controls = indirectControls ws.permissions ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  obtain ⟨seed, other, initialCall, registers, memory, events⟩ :=
    IndirectPermissionStages.initial_total ws state
  obtain ⟨controls, bodyCall, meaning⟩ := indirect_permission_body_total ws wp input seed other
  refine ⟨controls, other, ?_, meaning, registers, memory, events⟩
  have source := IndirectPermissionSource.source_eq ws wp input
  rw [el0Nonsecure_eq input el security] at source
  rw [source, IndirectPermissionStages.action_eq]
  simp only [IndirectPermissionStages.staged, Bind.bind, EStateM.bind, initialCall, bodyCall]

#print axioms indirect_permissions_total

end ArmCertWalk
