import ArmCertWalk.ComputedPermissionFacts
import ArmCertWalk.BasePermissionFacts

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

theorem computed_permission_body_total (ws : TTWState) (wp : S1TTWParams)
    (input : AccessDescriptor) (state : State) :
    ∃ controls other, ComputedPermissionStages.body ws wp input state = .ok controls other ∧
      computedControlProjection controls = computedControls ws.permissions wp state.regs ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  obtain ⟨base, middle, baseCall, baseMeaning, baseRegs, baseMem, baseEvents⟩ :=
    base_permissions_total ws wp (DirectPermissionSource.el0Nonsecure input) state rfl rfl
  obtain ⟨controls, other, afterCall, meaning, registers, memory, events⟩ :=
    after_base_permissions_total ws wp input base middle
  rw [baseMeaning, baseRegs] at meaning
  refine ⟨controls, other, ?_, meaning, registers.trans baseRegs,
    memory.trans baseMem, events.trans baseEvents⟩
  rw [ComputedPermissionStages.body_eq]
  unfold basePermissionCall at baseCall
  by_cases pie : (wp.pie == 1#1) = true <;>
    simp only [pie, Bool.false_eq_true, ↓reduceIte] at baseCall ⊢ <;>
    simp only [Bind.bind, EStateM.bind, baseCall, afterCall]

/-- Complete actual permission computation from current inputs, with active
overlay rights and WXN. All callee results and intermediate states are derived. -/
theorem computed_permissions_total (ws : TTWState) (wp : S1TTWParams)
    (input : AccessDescriptor) (state : State) (el : input.el = EL0)
    (security : input.ss = .SS_NonSecure) :
    ∃ controls other,
      AArch64_S1ComputePermissions .Regime_EL20 ws wp input state = .ok controls other ∧
      computedControlProjection controls = computedControls ws.permissions wp state.regs ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  obtain ⟨middle, initialCall, initialRegs, initialMem, initialEvents⟩ :=
    ComputedPermissionStages.initial_total ws state
  obtain ⟨controls, other, bodyCall, meaning, registers, memory, events⟩ :=
    computed_permission_body_total ws wp input middle
  rw [initialRegs] at meaning
  refine ⟨controls, other, ?_, meaning, registers.trans initialRegs,
    memory.trans initialMem, events.trans initialEvents⟩
  have source := ComputedPermissionSource.source_eq ws wp input
  rw [el0Nonsecure_eq input el security] at source
  rw [source, ComputedPermissionStages.action_eq]
  simp only [ComputedPermissionStages.staged, Bind.bind, EStateM.bind, initialCall, bodyCall]

#print axioms computed_permission_body_total
#print axioms computed_permissions_total

end ArmCertWalk
