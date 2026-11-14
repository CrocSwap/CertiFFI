import ArmCertWalk.PermissionFetchCheck
import ArmCertWalk.PermissionDataCheck

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

theorem permission_check_body_eq (fault : FaultRecord) (ws : TTWState)
    (wp : S1TTWParams) (input : AccessDescriptor) (controls : S1AccessControls) (state : State)
    (admissible : PermissionAdmissible ws.permissions wp (attributeProjection ws.memattrs)
      input (computedControlProjection controls)) :
    PermissionCheckSource.body fault ws wp input controls state = .ok fault state := by
  cases fetch : input.acctype == .AccessType_IFETCH with
  | false => exact permission_data_body_eq fault ws wp input controls state fetch admissible
  | true => exact permission_fetch_body_eq fault ws wp input controls state fetch admissible

/-- The actual checker preserves the incoming fault record when its executable
current-data policy passes. Computed rights and every callee success are derived. -/
theorem permission_check_total (fault : FaultRecord) (ws : TTWState) (wp : S1TTWParams)
    (input : AccessDescriptor) (state : State) (el : input.el = EL0)
    (security : input.ss = .SS_NonSecure)
    (admissible : PermissionAdmissible ws.permissions wp (attributeProjection ws.memattrs)
      input (computedControls ws.permissions wp state.regs)) :
    ∃ other, AArch64_S1CheckPermissions fault .Regime_EL20 ws wp input state = .ok fault other ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  obtain ⟨controls, other, computedCall, meaning, registers, memory, events⟩ :=
    computed_permissions_total ws wp input state el security
  have current : PermissionAdmissible ws.permissions wp (attributeProjection ws.memattrs)
      input (computedControlProjection controls) := by
    rw [meaning]
    exact admissible
  have bodyCall := permission_check_body_eq fault ws wp input controls other current
  refine ⟨other, ?_, registers, memory, events⟩
  have source := PermissionCheckSource.source_eq fault ws wp input
  rw [el0Nonsecure_eq input el security] at source
  rw [source, PermissionCheckSource.action_eq, el0Nonsecure_eq input el security]
  simp only [Bind.bind, EStateM.bind, computedCall, bodyCall]

#print axioms permission_check_body_eq
#print axioms permission_check_total

end ArmCertWalk
