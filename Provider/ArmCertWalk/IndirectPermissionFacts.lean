import ArmCertWalk.IndirectPermissionStages
import ArmCertWalk.IndirectPermissionMeaning

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

namespace ArmCertWalk

theorem pan_query_eq (state : State) :
    HavePANExt () state = .ok state.regs.FeatureImpl[51] state := rfl

theorem pstate_query_eq (state : State) :
    (readReg PSTATE : SailM ProcState) state = .ok state.regs.PSTATE state := rfl

/-- The indirect base stage reads PAN but does not change state or its EL0
result. The actual initial undefined fields remain in the seed and result. -/
theorem indirect_permission_body_total (ws : TTWState) (wp : S1TTWParams)
    (input : AccessDescriptor) (seed : IndirectPermissionStages.StageAcc) (state : State) :
    ∃ controls, IndirectPermissionStages.body ws wp input seed state = .ok controls state ∧
      baseControlProjection controls = indirectControls ws.permissions := by
  have has : HasUnprivileged .Regime_EL20 = true := by decide
  have nsSecure : (SecurityState.SS_NonSecure == .SS_Secure) = false := by decide
  have nsRoot : (SecurityState.SS_NonSecure == .SS_Root) = false := by decide
  have nsRealm : (SecurityState.SS_NonSecure == .SS_Realm) = false := by decide
  simp only [IndirectPermissionStages.body, has, ↓reduceIte,
    DirectPermissionSource.el0Nonsecure, EL0]
  generalize privilegedEq : indirectRights ws.permissions.ppi = privileged
  generalize userEq : indirectRights ws.permissions.upi = user
  rcases privileged with ⟨pgcs, pr, pw, px⟩
  rcases user with ⟨ugcs, ur, uw, ux⟩
  simp only [Bind.bind, EStateM.bind, pan_query_eq,
    Pure.pure, EStateM.pure]
  by_cases conflict : indirectConflict (pgcs, pr, pw, px) (ugcs, ur, uw, ux) = true <;>
    by_cases pan : (state.regs.FeatureImpl[51] && input.pan) = true
  all_goals
    simp only [indirectConflict] at conflict
    simp only [conflict, pan, ↓reduceIte]
    refine ⟨_, rfl, ?_⟩
    simp [baseControlProjection, indirectControls, indirectUserRights, indirectConflict,
      privilegedEq, userEq, conflict, nsSecure, nsRoot, nsRealm]

#print axioms pan_query_eq
#print axioms pstate_query_eq
#print axioms indirect_permission_body_total

end ArmCertWalk
