import ArmCertWalk.OverlayPermissionFacts
import ArmCertWalk.DirectPermissionTotal

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

theorem overlay_permissions_total (ws : TTWState) (input : AccessDescriptor)
    (state : State) (el : input.el = EL0) (security : input.ss = .SS_NonSecure) :
    ∃ controls other,
      AArch64_S1OverlayPermissions .Regime_EL20 ws input state = .ok controls other ∧
      overlayProjection controls = currentOverlayRights ws.permissions state.regs ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  obtain ⟨seed, other, initialCall, registers, memory, events⟩ :=
    OverlayPermissionStages.initial_total ws state
  obtain ⟨controls, bodyCall, meaning⟩ := overlay_permission_body_total ws input seed other
  rw [registers] at meaning
  refine ⟨controls, other, ?_, meaning, registers, memory, events⟩
  have source := OverlayPermissionSource.source_eq ws input
  rw [el0Nonsecure_eq input el security] at source
  rw [source, OverlayPermissionStages.action_eq]
  simp only [OverlayPermissionStages.staged, Bind.bind, EStateM.bind, initialCall, bodyCall]

#print axioms overlay_permissions_total

end ArmCertWalk
