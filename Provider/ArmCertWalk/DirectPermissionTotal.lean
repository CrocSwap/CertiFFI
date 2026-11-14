import ArmCertWalk.DirectPermissionFacts

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

theorem direct_permission_body_total (ws : TTWState) (wp : S1TTWParams)
    (input : AccessDescriptor) (seed : DirectPermissionStages.StageAcc) (state : State) :
    ∃ controls other, DirectPermissionStages.body ws wp input seed state = .ok controls other ∧
      baseControlProjection controls = directControls ws.permissions wp ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  have effect := direct_permission_body_effect ws wp input seed state
  cases actual : DirectPermissionStages.body ws wp input seed state with
  | error err other => simp only [actual, DirectPermissionEffect] at effect
  | ok controls other =>
    exact ⟨controls, other, rfl, by simpa only [actual, DirectPermissionEffect] using effect⟩

theorem el0Nonsecure_eq (input : AccessDescriptor) (el : input.el = EL0)
    (security : input.ss = .SS_NonSecure) : DirectPermissionSource.el0Nonsecure input = input := by
  cases input
  simp_all [DirectPermissionSource.el0Nonsecure]

/-- Current actual EL0/NS direct permissions. PAN feature and PSTATE.PAN are
arbitrary; all source queries and choices remain in the actual poststate. -/
theorem direct_permissions_total (ws : TTWState) (wp : S1TTWParams)
    (input : AccessDescriptor) (state : State) (el : input.el = EL0)
    (security : input.ss = .SS_NonSecure) :
    ∃ controls other,
      AArch64_S1DirectBasePermissions .Regime_EL20 ws wp input state = .ok controls other ∧
      baseControlProjection controls = directControls ws.permissions wp ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  obtain ⟨seed, middle, initialCall, initialRegs, initialMem, initialEvents⟩ :=
    DirectPermissionStages.initial_total ws state
  obtain ⟨controls, other, bodyCall, meaning, registers, memory, events⟩ :=
    direct_permission_body_total ws wp input seed middle
  refine ⟨controls, other, ?_, meaning, registers.trans initialRegs,
    memory.trans initialMem, events.trans initialEvents⟩
  have source := DirectPermissionSource.source_eq ws wp input
  rw [el0Nonsecure_eq input el security] at source
  rw [source, DirectPermissionStages.action_eq]
  simp only [DirectPermissionStages.staged, Bind.bind, EStateM.bind, initialCall, bodyCall]

#print axioms direct_permission_body_total
#print axioms el0Nonsecure_eq
#print axioms direct_permissions_total

end ArmCertWalk
