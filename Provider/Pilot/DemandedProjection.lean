import Pilot.StepCert
open Lean Meta
namespace StepEval.DemandedProjection

structure Result where
  expr : Expr
  proof : Expr

private def projectionView (e : Expr) : MetaM (Option (Expr × (Expr → Expr))) := do
  let args := e.getAppArgs
  match e.getAppFn with
  | .const fn _ =>
    let some info ← getProjectionFnInfo? fn | return none
    if args.size ≤ info.numParams then return none
    return some (args[info.numParams]!, fun v => mkAppN e.getAppFn (args.set! info.numParams v))
  | .proj n i receiver => return some (receiver, fun v => mkAppN (.proj n i v) args)
  | _ => return none

private def refl (e : Expr) : MetaM Result := return ⟨e, ← mkEqRefl e⟩

/-- Only projection receivers and their conditional joins are traversed.
    Selected data payloads and unrelated record fields remain opaque. -/
private partial def normalizeCore (fuel : IO.Ref Nat)
    (cache : IO.Ref (Std.HashMap Expr Result)) (e : Expr) : MetaM Result := do
  if let some result := (← cache.get)[e]? then
    let context ← getLCtx
    let used := (collectFVars (collectFVars {} result.expr) result.proof).fvarSet
    if used.toList.all (fun id => (context.find? id).isSome) then return result
  if (← fuel.get) == 0 then return ← refl e
  fuel.modify Nat.pred
  let cleaned := e.consumeMData.headBeta
  let result ← if cleaned == e then work e else do
    let tail ← normalizeCore fuel cache cleaned
    let initial ← mkExpectedTypeHint (← mkEqRefl e) (← mkEq e cleaned)
    pure ⟨tail.expr, ← mkEqTrans initial tail.proof⟩
  cache.modify (·.insert e result)
  return result
where
  finish (original : Expr) (step : Simp.Result) : MetaM Result := do
    if step.expr == original then return ← refl original
    let proof ← match step.proof? with
      | some proof => pure proof
      | none => mkExpectedTypeHint (← mkEqRefl original) (← mkEq original step.expr)
    let tail ← normalizeCore fuel cache step.expr
    return ⟨tail.expr, ← mkEqTrans proof tail.proof⟩
  work (value : Expr) : MetaM Result := do
    if let some (receiver,rebuild) ← projectionView value then
      if let some step ← StepEval.projectConstructor value then return ← finish value step
      if let some step ← StepEval.projectConditional value then return ← finish value step
      -- Reduce just a projection-valued receiver, never an arbitrary record.
      if (← projectionView receiver).isNone then return ← refl value
      let inner ← normalizeCore fuel cache receiver
      if inner.expr == receiver then return ← refl value
      let f ← withLocalDeclD `neededReceiver (← inferType receiver) fun v =>
        mkLambdaFVars #[v] (rebuild v)
      let .forallE _ _ codomain _ ← inferType f | return ← refl value
      -- Dependent field transport remains with the existing evaluator.
      if codomain.hasLooseBVar 0 then return ← refl value
      let proof ← mkCongrArg f inner.proof
      let out := rebuild inner.expr
      let tail ← normalizeCore fuel cache out
      return ⟨tail.expr, ← mkEqTrans proof tail.proof⟩
    let args := value.getAppArgs
    let dependent := value.getAppFn.isConstOf ``dite
    unless (dependent || value.getAppFn.isConstOf ``ite) && args.size == 5 do
      return ← refl value
    let condition := args[1]!
    let mut branches := #[]
    let mut proofs := #[]
    for side in [0:2] do
      let hypothesis := if side == 0 then condition else mkNot condition
      let (branch,proof) ← withLocalDeclD `projectionBranch hypothesis fun h => do
        let original := if dependent then mkApp args[side+3]! h else args[side+3]!
        let result ← normalizeCore fuel cache original
        return (← mkLambdaFVars #[h] result.expr, ← mkLambdaFVars #[h] result.proof)
      branches := branches.push branch
      proofs := proofs.push proof
    let lemma := if dependent then ``StepRuntime.split_value_dite else ``StepRuntime.split_value_ite
    let proof ← mkAppM lemma #[condition,args[3]!,args[4]!,branches[0]!,branches[1]!,proofs[0]!,proofs[1]!]
    let some (_,lhs,out) := (← inferType proof).consumeMData.eq? | throwError "projection split is not an equation"
    unless ← isDefEq lhs value do throwError "projection split changed its input"
    let left := branches[0]!.bindingBody!
    let right := branches[1]!.bindingBody!
    if !left.hasLooseBVars && !right.hasLooseBVars && left == right then
      let merge ← mkAppM ``StepRuntime.merge_dite #[condition,left]
      return ⟨left, ← mkEqTrans proof merge⟩
    return ⟨out,proof⟩

def normalize? (e : Expr) : MetaM (Option Simp.Result) := do
  if (← projectionView e).isNone then return none
  let fuel ← IO.mkRef 512
  let cache ← IO.mkRef ({} : Std.HashMap Expr Result)
  let result ← normalizeCore fuel cache e
  if result.expr == e then return none
  return some {expr := result.expr,proof? := some result.proof}
end StepEval.DemandedProjection
