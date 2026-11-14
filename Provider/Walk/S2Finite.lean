import Lean
import ArmFull
open Lean Meta Elab Tactic
/- Local proof assembly for a generated flat-enum casesOn result. No computation
   is trusted: ordinary generalize/cases/rfl construct a kernel-checked proof. -/
elab "s2_cases_constraint" : tactic => do
  let goal ← getMainGoal
  let goals ← goal.withContext do
    let target ← goal.getType
    let some occurrence := target.find? (fun e => e.isAppOf ``ArmFull.Constraint.casesOn)
      | throwError "no Constraint.casesOn in target"
    let major := occurrence.getAppArgs[1]!
    let (vars, next) ← goal.generalize #[{expr := major, xName? := some `constraintValue}]
    let branches ← next.cases vars[0]!
    pure (branches.toList.map (·.mvarId))
  replaceMainGoal goals
