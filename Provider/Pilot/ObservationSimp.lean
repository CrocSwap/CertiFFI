import Pilot.StepCert
open Lean Meta Elab Tactic
namespace ObservationSimp
initialize unfoldCache : IO.Ref (Std.HashMap Name Name) ← IO.mkRef {}
def unfoldSelected (e : Expr) (names : Array Name) : MetaM (Option Simp.Result) := do
  let .const n levels := e.getAppFn | return none
  unless names.contains n do return none
  let ci ← getConstInfo n
  let some value := ci.value? | return none
  let cached := (← unfoldCache.get)[n]?
  let th ← match cached with
    | some th => if (← getEnv).contains th then pure th else pure Name.anonymous
    | none => pure Name.anonymous
  let th ← if !th.isAnonymous then pure th else do
    let fn := mkConst n (ci.levelParams.map Level.param)
    let r ← StepEval.certify fn {expr := value} ci.levelParams
    let some pf := r.proof? | throwError "unchanged observation definition"
    let th := pf.getAppFn.constName!
    unfoldCache.modify (·.insert n th)
    pure th
  let mut pf := mkConst th levels
  for a in e.getAppArgs do pf ← mkCongrFun pf a
  let out := (mkAppN (value.instantiateLevelParams ci.levelParams levels) e.getAppArgs).headBeta
  return some {expr := out, proof? := some pf}
elab "observe_simp" "[" names:ident,* "]" : tactic => do
  let selected ← names.getElems.mapM fun id => do
    realizeGlobalConstNoOverloadWithInfo id
  let g ← getMainGoal
  let next ← g.withContext do
    let mut thms ← getSimpTheorems
    for d in (← getLCtx) do
      unless d.isImplementationDetail do
        if ← isProp d.type then thms ← thms.add (.fvar d.fvarId) #[] d.toExpr
    let ctx ← Simp.mkContext {maxSteps := 20000, dsimp := true, decide := false}
      #[thms] (← getSimpCongrTheorems)
    let methods := Simp.mkDefaultMethodsCore #[← Simp.getSimprocs]
    let pre : Simp.Simproc := fun e => do
      if let some r ← unfoldSelected e selected then return .visit r
      if let some r ← StepEval.projectConstructor e then return .visit r
      if let some r ← StepEval.projectConditional e then return .visit r
      if !e.hasFVar && !e.hasLooseBVars && !e.hasMVar &&
          (← inferType e).isConstOf ``Bool then
        let out ← StepEval.closedWhnf e
        if out != e && (out.isConstOf ``Bool.true || out.isConstOf ``Bool.false) then
          return .visit (← StepEval.certify e {expr := out})
      if let .const n _ := e.getAppFn then
        if let .ctorInfo ci ← getConstInfo n then
          if (getStructureInfo? (← getEnv) ci.induct).isSome then
            return .done {expr := e}
      methods.pre e
    let ty ← g.getType
    let (r, _) ← Simp.main ty ctx (methods := {methods with pre})
    if r.expr.isTrue then
      g.assign (← mkOfEqTrue (← r.getProof))
      pure none
    else return some (← applySimpResultToTarget g ty r)
  replaceMainGoal next.toList
end ObservationSimp
