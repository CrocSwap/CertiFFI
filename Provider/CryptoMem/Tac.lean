import Lean
open Lean Meta Elab Tactic

/-- `name_state h as x`: for `h : f ... st = rhs`, generalize the last argument `st` of the LHS
into a fresh variable `x` (in the goal and in `h`), recording `hx : st = x` (armcert-crypto). -/
elab "name_state " h:ident " as " x:ident : tactic => withMainContext do
  let decl ← getLocalDeclFromUserName h.getId
  let ty ← instantiateMVars decl.type
  let some (_, lhs, _) := ty.eq? | throwError "name_state: not an equation"
  let st := lhs.appArg!
  let stx ← Term.exprToSyntax st
  let hx := mkIdent (x.getId.appendBefore "h")
  evalTactic (← `(tactic| generalize $hx:ident : $stx = $x at $h:ident ⊢))

/-- `name_call_state f as x`: find the first application of the constant `f` in the goal whose
last argument is a closed-in-context term, and generalize that last argument (the state) into a
fresh variable `x`, recording `hx : st = x` (armcert-crypto). -/
elab "name_call_state " f:ident " as " x:ident : tactic => withMainContext do
  let fn ← realizeGlobalConstNoOverloadWithInfo f
  let t ← instantiateMVars (← getMainTarget)
  let some e := t.find? (fun e => e.isAppOf fn && !e.appArg!.hasLooseBVars)
    | throwError "name_call_state: no application of {fn}"
  let st := e.appArg!
  let stx ← Term.exprToSyntax st
  let hx := mkIdent (x.getId.appendBefore "h")
  evalTactic (← `(tactic| generalize $hx:ident : $stx = $x))

/-- `reduce_closed_nat`: replace every closed subterm of the goal headed by `Sail.Int.toNatChecked`
by its value (a Nat literal, computed by whnf), via `congrArg` on `Eq.refl` — the kernel re-checks
the definitional equality (armcert-crypto). -/
elab "reduce_closed_nat" : tactic => withMainContext do
  for _ in [0:20] do
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    let some e := t.find? (fun e => e.isAppOf `Sail.Int.toNatChecked && !e.hasLooseBVars && !e.hasFVar &&
        !e.hasMVar && e.getAppNumArgs == 1)
      | return
    let v ← withTransparency .all <| whnf e
    let some n ← (Meta.evalNat v).run | throwError "reduce_closed_nat: cannot evaluate {e}"
    let lit := mkNatLit n
    let motive ← withLocalDeclD `z (mkConst ``Nat) fun z => do
      mkLambdaFVars #[z] (t.replace fun x => if x == e then some z else none)
    let pf ← mkExpectedTypeHint (← mkEqRefl e) (← mkEq e lit)
    let newT := (mkApp motive lit).headBeta
    replaceMainGoal [← g.replaceTargetEq newT (← mkCongrArg motive pf)]
