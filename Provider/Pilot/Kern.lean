import Lean
/-!
# Kernel-reduction helpers

`kernel_rfl` closes a goal `lhs = rhs` by adding an auxiliary theorem whose proof is `Eq.refl lhs`,
checked by the Lean kernel only (no elaborator defeq check, no simp). The kernel unfolds both sides
lazily; with concrete configuration registers every control decision of the Sail code reduces, and
the symbolic parts (GPRs, VA, memory, oracle) are carried along as data.

`#kexplore e` (exploration only, not used in proofs): weak-head normalises the body of the lambda `e`
with `Meta.whnf` (all transparency) and prints the head / the result, to find out which register
reads are still symbolic.
-/
open Lean Meta Elab Tactic Command Term

namespace Kern

def kernelRflCore (g : MVarId) (hb : Nat := 0) : MetaM Unit := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let some (_, lhs, _) := t.eq? | throwError "kernel_rfl: goal is not an equality"
  -- abstract the local context the goal depends on (in context order)
  let lctx ← getLCtx
  let mut fvs : Std.HashSet FVarId := (collectFVars {} t).fvarSet.toList.foldl (·.insert ·) {}
  -- close under dependencies (types of used locals)
  let mut changed := true
  while changed do
    changed := false
    for d in lctx do
      if fvs.contains d.fvarId then
        for f in (collectFVars {} (← instantiateMVars d.type)).fvarSet.toList do
          unless fvs.contains f do fvs := fvs.insert f; changed := true
  let xs := lctx.foldl (init := #[]) fun acc d =>
    if fvs.contains d.fvarId && !d.isImplementationDetail then acc.push d.toExpr else acc
  let ty ← instantiateMVars (← mkForallFVars xs t)
  let pf ← instantiateMVars (← mkLambdaFVars xs (← mkEqRefl lhs))
  let t0 ← IO.monoMsNow
  let n ← try
    withOptions (fun o => o.set `maxHeartbeats hb |>.setBool `Elab.async false) <|
      mkAuxLemma [] ty pf (cache := false)
  catch ex =>
    throwError m!"kernel_rfl failed after {(← IO.monoMsNow) - t0} ms: {ex.toMessageData}"
  let t1 ← IO.monoMsNow
  if (← IO.getEnv "KERN_LOG").isSome then logInfo m!"kernel_rfl: {t1 - t0} ms"
  g.assign (mkAppN (mkConst n) xs)

elab "kernel_rfl" : tactic => do
  let g ← getMainGoal
  kernelRflCore g
  replaceMainGoal []

/-- exploration: whnf the lambda body; print result head (and the value of an `.ok`). -/
elab "#kexplore " t:term : command => liftTermElabM do
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  lambdaTelescope e fun _ body => do
    let t0 ← IO.monoMsNow
    let r ← withTransparency .all <| whnf body
    let t1 ← IO.monoMsNow
    let fn := r.getAppFn
    logInfo m!"whnf in {t1 - t0} ms; head = {fn}; nargs={r.getAppNumArgs}"
    if fn.isConstOf ``EStateM.Result.ok || fn.isConstOf ``EStateM.Result.error then
      let a := r.getAppArgs
      let v ← withTransparency .all <| whnf a[a.size - 2]!
      withOptions (fun o => o.set `pp.deepTerms false |>.set `pp.proofs false |>.set `pp.maxSteps (20000 : Nat)) do
        logInfo m!"value whnf: {v}"
    else
      withOptions (fun o => o.set `pp.deepTerms false |>.set `pp.proofs false |>.set `pp.maxSteps (5000 : Nat)) do
        logInfo m!"stuck term: {r}"

end Kern
