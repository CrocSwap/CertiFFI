import Walk.S1EL10PermsCallees
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open Lean Meta Elab Tactic
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1EL10LeafPerms
open S1Normality
private partial def solveNormal (fuel : Nat) : TacticM Unit := do
  if fuel == 0 then throwError "leaf normality search depth exhausted"
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  if ty.isForall then
    evalTactic (← `(tactic| intro x))
    solveNormal (fuel - 1)
    return
  let saved ← saveState
  try
    evalTactic (← `(tactic| solve | first
      | exact S1Normality.pure_normal _
      | exact S1Normality.occ_normal _
      | exact S1EL10PermsCallees.int_normal _
      | exact S1EL10PermsCallees.el2_normal
      | exact S1EL10PermsCallees.poe_normal
      | exact S1EL10PermsCallees.e0poe_normal _
      | exact S1Normality.walk_normal _
      | exact S1Normality.address_normal _
      | exact S1Normality.bits_normal _ _
      | (apply S1Normality.assert_normal; decide)
      | (apply S1Normality.attrs_normal; exact S1MAIRKernel.valid _)
      | (apply S1Normality.permissions_normal; assumption)))
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
elab "el10_permissions_normality" : tactic => solveNormal 200

theorem normal (permissions : Permissions) (d : BitVec 64) (wp : S1TTWParams)
    (hD128 : wp.d128 = 0#1) :
    Normal (AArch64_S1ApplyOutputPerms permissions d .Regime_EL10 wp) := by
  have h01 : ((0#1) == (1#1)) = false := by decide
  have hUP : HasUnprivileged .Regime_EL10 = true := by decide
  have h10 : ((.Regime_EL10 : Regime) == .Regime_EL10) = true := by decide
  have ha7 : (7 <b Sail.BitVec.length d) = true := by
    change (7 <b (64 : Int)) = true
    decide
  have ha54 : (54 <b Sail.BitVec.length d) = true := by
    change (54 <b (64 : Int)) = true
    decide
  have ha51 : (51 <b Sail.BitVec.length d) = true := by
    change (51 <b (64 : Int)) = true
    decide
  have ha62 : (62 <b Sail.BitVec.length d) = true := by
    change (62 <b (64 : Int)) = true
    decide
  have assert_true (message : String) :
      ArmFull.assert true message = (pure () : SailM Unit) := rfl
  unfold AArch64_S1ApplyOutputPerms
  simp only [hD128, h01, hUP, h10, ha7, ha54, ha51, ha62, assert_true,
    Bool.not_true, Bool.not_false, Bool.true_and, Bool.and_true,
    Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte, pure_bind]
  el10_permissions_normality
#print axioms normal
end S1EL10LeafPerms
