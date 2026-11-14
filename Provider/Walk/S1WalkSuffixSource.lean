import Pilot.S1WalkSource
open Lean Meta Elab Command
namespace S1WalkSuffixSource
/- Name the actual loop0 continuation and replace only that subterm. Ordinary
   kernel-checked definitions and reflexivity tie it to the complete source. -/
private partial def replaceGuard (locals : Array Expr) (e : Expr) : MetaM (Expr × Nat) := do
  if e.isAppOf ``Bind.bind && decide (e.getAppNumArgs ≥ 2) then
    let args := e.getAppArgs
    let computation := args[args.size - 2]!
    let isBool := match args.back!.consumeMData with
      | .lam _ ty _ _ => ty.isConstOf ``Bool
      | _ => false
    if isBool && (computation.find? (·.isConstOf ``ArmFull.Register.__tlb_enabled)).isSome then
      let continuation := computation
      let params ← S2SourceLoops.dependencies locals continuation
      let value ← mkLambdaFVars params continuation
      let type ← inferType value
      let name := `S1WalkSuffixSource.cacheGuard
      addDecl (.defnDecl {
        name := name
        levelParams := []
        type := type
        value := ShareCommon.shareCommon value
        hints := .abbrev
        safety := .safe })
      return (mkAppN e.getAppFn (args.set! (args.size - 2) (mkAppN (mkConst name) params)), 1)
  match e with
  | .lam name ty body bi =>
    withLocalDecl name bi ty fun x => do
      let (value, n) ← replaceGuard (locals.push x) (body.instantiate1 x)
      return (← mkLambdaFVars #[x] value, n)
  | .letE name ty value body nondep =>
    let (v, n) ← replaceGuard locals value
    withLocalDeclD name ty fun x => do
      let (body', k) ← replaceGuard (locals.push x) (body.instantiate1 x)
      return (.letE name ty v (body'.abstract #[x]) nondep, n + k)
  | .app f a =>
    let (f', n) ← replaceGuard locals f
    let (a', k) ← replaceGuard locals a
    return (.app f' a', n + k)
  | .mdata md body =>
    let (value, n) ← replaceGuard locals body
    return (.mdata md value, n)
  | .proj name index body =>
    let (value, n) ← replaceGuard locals body
    return (.proj name index value, n)
  | _ => return (e, 0)

private partial def replaceSuffix (locals : Array Expr) (e : Expr) : MetaM (Expr × Nat) := do
  if e.isAppOf ``Bind.bind && decide (e.getAppNumArgs ≥ 2) then
    let args := e.getAppArgs
    if args.any (fun a => a.isAppOf ``S1WalkSource.named.loop0) then
      let (continuation, guardCount) ← replaceGuard locals args.back!
      unless guardCount == 1 do throwError "expected one post-loop TLB guard"
      let params ← S2SourceLoops.dependencies locals continuation
      let value ← mkLambdaFVars params continuation
      let type ← inferType value
      let name := `S1WalkSuffixSource.suffix
      addDecl (.defnDecl {
        name := name
        levelParams := []
        type := type
        value := ShareCommon.shareCommon value
        hints := .abbrev
        safety := .safe })
      return (mkAppN e.getAppFn (args.set! (args.size - 1) (mkAppN (mkConst name) params)), 1)
  match e with
  | .lam name ty body bi =>
    withLocalDecl name bi ty fun x => do
      let (value, n) ← replaceSuffix (locals.push x) (body.instantiate1 x)
      return (← mkLambdaFVars #[x] value, n)
  | .letE name ty value body nondep =>
    let (v, n) ← replaceSuffix locals value
    withLocalDeclD name ty fun x => do
      let (body', k) ← replaceSuffix (locals.push x) (body.instantiate1 x)
      return (.letE name ty v (body'.abstract #[x]) nondep, n + k)
  | .app f a =>
    let (f', n) ← replaceSuffix locals f
    let (a', k) ← replaceSuffix locals a
    return (.app f' a', n + k)
  | .mdata md body =>
    let (value, n) ← replaceSuffix locals body
    return (.mdata md value, n)
  | .proj name index body =>
    let (value, n) ← replaceSuffix locals body
    return (.proj name index value, n)
  | _ => return (e, 0)

elab "name_s1_walk_suffix" : command => liftTermElabM do
  let source ← getConstInfo ``S1WalkSource.named
  let some original := source.value? | throwError "source has no value"
  let (value, nFound) ← replaceSuffix #[] original
  unless nFound == 1 do throwError "expected exactly one loop0 continuation"
  let name := `S1WalkSuffixSource.withSuffix
  addDecl (.defnDecl {
    name := name
    levelParams := []
    type := source.type
    value := ShareCommon.shareCommon value
    hints := .abbrev
    safety := .safe })
  let type ← mkEq (mkConst ``S1WalkSource.named) (mkConst name)
  addDecl (.thmDecl {
    name := `S1WalkSuffixSource.equation
    levelParams := []
    type := type
    value := ← mkEqRefl (mkConst ``S1WalkSource.named) })
name_s1_walk_suffix
#check suffix
#check cacheGuard
#print axioms equation
end S1WalkSuffixSource
