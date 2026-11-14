import Walk.S1WalkSuffixSource
open Lean Meta Elab Command
namespace S1WalkTailSource
private partial def nameTail (locals : Array Expr) (e : Expr) : MetaM (Expr × Nat) := do
  if e.isAppOf ``Bind.bind && decide (e.getAppNumArgs ≥ 2) then
    let args := e.getAppArgs
    if args.any (fun a => a.isAppOf ``S1WalkSource.named.loop0) then
      let params ← S2SourceLoops.dependencies locals e
      let value ← mkLambdaFVars params e
      addDecl (.defnDecl {
        name := `S1WalkTailSource.tail
        levelParams := []
        type := ← inferType value
        value := ShareCommon.shareCommon value
        hints := .abbrev
        safety := .safe })
      return (mkAppN (mkConst `S1WalkTailSource.tail) params, 1)
  match e with
  | .lam name ty body bi =>
    withLocalDecl name bi ty fun x => do
      let (value, n) ← nameTail (locals.push x) (body.instantiate1 x)
      return (← mkLambdaFVars #[x] value, n)
  | .letE name ty value body nondep =>
    let (v, n) ← nameTail locals value
    withLocalDeclD name ty fun x => do
      let (body', k) ← nameTail (locals.push x) (body.instantiate1 x)
      return (.letE name ty v (body'.abstract #[x]) nondep, n + k)
  | .app f a =>
    let (f', n) ← nameTail locals f
    let (a', k) ← nameTail locals a
    return (.app f' a', n + k)
  | .mdata md body =>
    let (value, n) ← nameTail locals body
    return (.mdata md value, n)
  | .proj name index body =>
    let (value, n) ← nameTail locals body
    return (.proj name index value, n)
  | _ => return (e, 0)

elab "name_actual_s1_tail" : command => liftTermElabM do
  let source ← getConstInfo ``S1WalkSuffixSource.withSuffix
  let some original := source.value? | throwError "source has no value"
  let (value, nFound) ← nameTail #[] original
  unless nFound == 1 do throwError "expected exactly one S1 source tail"
  addDecl (.defnDecl {
    name := `S1WalkTailSource.withTail
    levelParams := []
    type := source.type
    value := ShareCommon.shareCommon value
    hints := .abbrev
    safety := .safe })
  addDecl (.thmDecl {
    name := `S1WalkTailSource.equation
    levelParams := []
    type := ← mkEq (mkConst ``S1WalkSource.named) (mkConst `S1WalkTailSource.withTail)
    value := ← mkEqRefl (mkConst ``S1WalkSource.named) })
name_actual_s1_tail
#check tail
#print axioms equation
end S1WalkTailSource
