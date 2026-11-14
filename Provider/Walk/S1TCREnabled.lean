import Walk.S1AIEGuard
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmFull.Register
open Lean Meta Elab Tactic
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1TCREnabled
open S1Normality

theorem feature_normal : Normal (HaveFeatTCR2 ()) := by
  intro s
  exact ⟨_, s, S1AIEGuard.feature_tcr2 s, rfl, rfl, rfl⟩
theorem hcx_feature_normal : Normal (HaveFeatHCX ()) := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩
theorem scr_normal : Normal (readReg SCR_EL3) := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩
theorem hcrx_read_normal : Normal (readReg HCRX_EL2) := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

private partial def solveNormal (fuel : Nat) : TacticM Unit := do
  if fuel == 0 then throwError "TCR guard normality depth exhausted"
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  if ty.isForall then
    evalTactic (← `(tactic| intro x))
    solveNormal (fuel - 1)
    return
  let saved ← saveState
  try
    evalTactic (← `(tactic| solve | first
      | assumption
      | exact S1Normality.pure_normal _
      | exact S1EL10PermsCallees.el2_normal
      | exact feature_normal
      | exact hcx_feature_normal
      | exact scr_normal
      | exact hcrx_read_normal))
    return
  catch _ => saved.restore
  evalTactic (← `(tactic| first
    | apply S1Normality.bind_normal
    | apply S1Normality.map_normal
    | apply S1Normality.ite_normal))
  let goals ← getGoals
  for branch in goals do
    setGoals [branch]
    solveNormal (fuel - 1)
  setGoals []
elab "tcr_guard_normality" : tactic => solveNormal 100

theorem hcx_normal : Normal (IsHCRXEL2Enabled ()) := by
  unfold IsHCRXEL2Enabled
  tcr_guard_normality

theorem normal1 : Normal (IsTCR2EL1Enabled ()) := by
  have h : Normal (IsHCRXEL2Enabled ()) := hcx_normal
  unfold IsTCR2EL1Enabled
  tcr_guard_normality

theorem normal2 : Normal (IsTCR2EL2Enabled ()) := by
  unfold IsTCR2EL2Enabled
  tcr_guard_normality
#print axioms normal1
#print axioms normal2
end S1TCREnabled
