import GetGuestFields.CalleeNormal
open Lean Meta Elab Tactic
namespace GetGuestFields.ProofTool
private partial def solve (fuel : Nat) : TacticM Unit := do
  if fuel == 0 then throwError "field preservation depth exhausted"
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  if ty.isForall then
    evalTactic (← `(tactic| intro x))
    solve (fuel - 1)
    return
  let saved ← saveState
  try
    evalTactic (← `(tactic| solve | first
      | exact GetGuestFields.CalleeNormal.read _
      | exact GetGuestFields.CalleeNormal.occurrence _
      | exact GetGuestFields.CalleeNormal.unknown _
      | exact GetGuestFields.CalleeNormal.tcr2
      | exact GetGuestFields.CalleeNormal.sctlr2
      | exact GetGuestFields.CalleeNormal.el2
      | exact GetGuestFields.CalleeNormal.Have128BitDescriptorExt
      | exact GetGuestFields.CalleeNormal.HaveSVE
      | exact GetGuestFields.CalleeNormal.HaveTME
      | exact GetGuestFields.CalleeNormal.HavePACExt
      | exact GetGuestFields.CalleeNormal.HaveE0PDExt
      | exact GetGuestFields.CalleeNormal.AArch64_HaveHPDExt
      | exact GetGuestFields.CalleeNormal.HaveMTE4Ext
      | exact GetGuestFields.CalleeNormal.HaveAIEExt
      | exact GetGuestFields.CalleeNormal.HaveRME
      | exact GetGuestFields.CalleeNormal.HaveSecureEL2Ext
      | exact GetGuestFields.CalleeNormal.HaveMTE2Ext
      | exact GetGuestFields.CalleeNormal.HaveTrapLoadStoreMultipleDeviceExt
      | exact GetGuestFields.CalleeNormal.HaveFeatCMOW
      | exact GetGuestFields.CalleeNormal.HaveAccessFlagUpdateExt
      | exact GetGuestFields.CalleeNormal.HaveDirtyBitModifierExt
      | exact GetGuestFields.CalleeNormal.Have52BitIPAAndPASpaceExt
      | exact GetGuestFields.CalleeNormal.HaveS1PIExt
      | exact GetGuestFields.CalleeNormal.HavePAN3Ext
      | exact GetGuestFields.CalleeNormal.HaveTHExt
      | exact GetGuestFields.CalleeNormal.HaveAccessFlagUpdateForTableExt
      | exact GetGuestFields.CalleeNormal.HaveFeatMEC
      | exact GetGuestFields.CalleeNormal.TTBR0
      | exact GetGuestFields.CalleeNormal.TTBR1
      | exact GetGuestFields.CalleeNormal.TG0 _
      | exact GetGuestFields.CalleeNormal.TG1 _
      | exact GetGuestFields.CalleeNormal.Constraint
      | exact S1Normality.pure_normal _
      | (apply GetGuestFields.Result.pure_returns; simp [GetGuestFields.active])))
    return
  catch _ => saved.restore
  evalTactic (← `(tactic| first
    | apply GetGuestFields.Result.bind_returns
    | apply GetGuestFields.Result.ite_returns
    | apply S1Normality.bind_normal
    | apply S1Normality.ite_normal
    | split))
  let goals ← getGoals
  for branch in goals do
    setGoals [branch]
    solve (fuel - 1)
  setGoals []
elab "preserve_guest_fields" : tactic => solve 200
end GetGuestFields.ProofTool
