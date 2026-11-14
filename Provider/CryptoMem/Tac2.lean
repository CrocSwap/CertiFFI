import Lean
open Lean Meta Elab Tactic

/-- `name_call_arg f k as x`: find the first application of the constant `f` in the goal whose
k-th-from-last argument (0 = last) is closed in context, and generalize that argument into a
fresh variable `x`, recording `hx : arg = x` (armcert-crypto). -/
elab "name_call_arg " f:ident k:num " as " x:ident : tactic => withMainContext do
  let fn ← realizeGlobalConstNoOverloadWithInfo f
  let k := k.getNat
  let t ← instantiateMVars (← getMainTarget)
  let ok (e : Expr) : Bool :=
    e.isAppOf fn && e.getAppNumArgs > k && !(e.getAppArgs[e.getAppNumArgs - 1 - k]!).hasLooseBVars
  let some e := t.find? ok | throwError "name_call_arg: no application of {fn}"
  let a := e.getAppArgs[e.getAppNumArgs - 1 - k]!
  let stx ← Term.exprToSyntax a
  let hx := mkIdent (x.getId.appendBefore "h")
  evalTactic (← `(tactic| generalize $hx:ident : $stx = $x))

/-- `name_app_state f n as x`: like `name_call_state`, but only matches applications of `f` with
exactly `n` arguments (so a partially applied `f ()` inside a bind is skipped) (armcert-crypto). -/
elab "name_app_state " f:ident n:num " as " x:ident : tactic => withMainContext do
  let fn ← realizeGlobalConstNoOverloadWithInfo f
  let n := n.getNat
  let t ← instantiateMVars (← getMainTarget)
  let some e := t.find? (fun e => e.isAppOf fn && e.getAppNumArgs == n && !e.appArg!.hasLooseBVars)
    | throwError "name_app_state: no {n}-ary application of {fn}"
  let st := e.appArg!
  let stx ← Term.exprToSyntax st
  let hx := mkIdent (x.getId.appendBefore "h")
  evalTactic (← `(tactic| generalize $hx:ident : $stx = $x))

/-- `reduce_closed_nat2`: like `reduce_closed_nat`, but abstracts EVERY closed
`Sail.Int.toNatChecked` subterm that evaluates to the same literal into one variable, checks that
the motive is type-correct, first changes the goal (defeq) so all those occurrences are the same
term, then rewrites by `congrArg` (kernel-checked). Skips a group whose motive is not
type-correct (armcert-crypto). -/
elab "reduce_closed_nat2" : tactic => withMainContext do
  let mut skip : Array Expr := #[]
  for _ in [0:40] do
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    let isCand (e : Expr) : Bool := e.isAppOf `Sail.Int.toNatChecked && !e.hasLooseBVars && !e.hasFVar &&
        !e.hasMVar && e.getAppNumArgs == 1
    let some e := t.find? (fun e => isCand e && !skip.contains e) | return
    let v ← withTransparency .all <| whnf e
    let some n ← (Meta.evalNat v).run | throwError "reduce_closed_nat2: cannot evaluate {e}"
    -- collect all candidate occurrences with the same value
    let mut grp : Array Expr := #[e]
    let mut seen : Array Expr := #[e]
    let mut tt := t
    for _ in [0:200] do
      let some e2 := tt.find? (fun x => isCand x && !seen.contains x) | break
      seen := seen.push e2
      let v2 ← withTransparency .all <| whnf e2
      if let some n2 ← (Meta.evalNat v2).run then
        if n2 == n then grp := grp.push e2
      tt := tt.replace fun x => if x == e2 then some (mkConst ``Unit.unit) else none
    let lit := mkNatLit n
    let motive ← withLocalDeclD `z (mkConst ``Nat) fun z => do
      mkLambdaFVars #[z] (t.replace fun x => if grp.contains x then some z else none)
    if !(← isTypeCorrect motive) then
      skip := skip ++ grp
      continue
    let t1 := (mkApp motive e).headBeta
    let g1 ← g.replaceTargetDefEq t1
    let pf ← mkExpectedTypeHint (← mkEqRefl e) (← mkEq e lit)
    let newT := (mkApp motive lit).headBeta
    replaceMainGoal [← g1.replaceTargetEq newT (← mkCongrArg motive pf)]
