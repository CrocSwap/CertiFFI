import Lean
import ArmFull
open Lean Meta Elab Command

namespace S2SourceLoops
/- Name source subterms without evaluating them. Ordinary checked definitions
   and reflexivity establish the equation with the original source function. -/
def dependencies (locals : Array Expr) (e : Expr) : MetaM (Array Expr) := do
  let mut used := collectFVars {} e
  let mut kept := #[]
  for x in locals.reverse do
    if used.fvarSet.contains x.fvarId! then
      kept := kept.push x
      used := collectFVars used (← inferType x)
  return kept.reverse

partial def nameLoops (base : Name) (arity : Nat) (locals : Array Expr)
    (e : Expr) (next : Nat) : MetaM (Expr × Nat) := do
  if e.isAppOf ``ArmFull.sailUntilFuelM && e.getAppNumArgs == arity then
    let args := e.getAppArgs
    let index := arity - 1
    let (body, after) ← nameLoops base arity locals args[index]! (next + 1)
    let params ← dependencies locals body
    let value ← mkLambdaFVars params body
    let type ← inferType value
    let name := base.str s!"body{next}"
    addDecl (.defnDecl {
      name := name
      levelParams := []
      type := type
      value := ShareCommon.shareCommon value
      hints := .abbrev
      safety := .safe })
    let call := mkAppN e.getAppFn (args.set! index (mkAppN (mkConst name) params))
    let callParams ← dependencies locals call
    let callValue ← mkLambdaFVars callParams call
    let callType ← inferType callValue
    let callName := base.str s!"loop{next}"
    addDecl (.defnDecl {
      name := callName
      levelParams := []
      type := callType
      value := ShareCommon.shareCommon callValue
      hints := .abbrev
      safety := .safe })
    return (mkAppN (mkConst callName) callParams, after)
  match e with
  | .lam name type body bi =>
    withLocalDecl name bi type fun x => do
      let (body', after) ← nameLoops base arity (locals.push x) (body.instantiate1 x) next
      return (← mkLambdaFVars #[x] body', after)
  | .letE name type value body nondep =>
    let (value', n) ← nameLoops base arity locals value next
    withLocalDeclD name type fun x => do
      let (body', after) ← nameLoops base arity (locals.push x) (body.instantiate1 x) n
      return (.letE name type value' (body'.abstract #[x]) nondep, after)
  | .app f a =>
    let (f', n) ← nameLoops base arity locals f next
    let (a', after) ← nameLoops base arity locals a n
    return (.app f' a', after)
  | .mdata data body =>
    let (body', after) ← nameLoops base arity locals body next
    return (.mdata data body', after)
  | .proj name index body =>
    let (body', after) ← nameLoops base arity locals body next
    return (.proj name index body', after)
  | _ => return (e, next)

def nameSource (sourceName targetName : Name) (expected : Nat) : TermElabM Unit := do
    let info ← getConstInfo sourceName
    unless info.levelParams.isEmpty do throwError "expected a monomorphic source"
    let some original := info.value? | throwError "source has no definition"
    let loop ← getConstInfo ``ArmFull.sailUntilFuelM
    let arity ← forallTelescope loop.type fun xs _ => pure xs.size
    let (value, count) ← nameLoops targetName arity #[] original 0
    unless count == expected do throwError "expected {expected} source loops, found {count}"
    addDecl (.defnDecl {
      name := targetName
      levelParams := []
      type := info.type
      value := ShareCommon.shareCommon value
      hints := .abbrev
      safety := .safe })
    let type ← mkEq (mkConst sourceName) (mkConst targetName)
    addDecl (.thmDecl {
      name := targetName.str "equation"
      levelParams := []
      type := type
      value := ← mkEqRefl (mkConst sourceName) })
    logInfo m!"named {count} source loop bodies; reflexive source equation kernel checked"

elab "s2_name_source_loops " source:ident " as " target:ident : command => do
  let sourceName ← resolveGlobalConstNoOverload source
  let targetName := (← getCurrNamespace) ++ target.getId
  liftTermElabM <| nameSource sourceName targetName 2

elab "name_source_loops " source:ident " as " target:ident " count " expected:num : command => do
  let sourceName ← resolveGlobalConstNoOverload source
  let targetName := (← getCurrNamespace) ++ target.getId
  liftTermElabM <| nameSource sourceName targetName expected.getNat
end S2SourceLoops

elab "s2_parameterize_source_tail " source:ident " replacing " tail:ident
    " as " target:ident : command => do
  let sourceName ← resolveGlobalConstNoOverload source
  let tailName ← resolveGlobalConstNoOverload tail
  let targetName := (← getCurrNamespace) ++ target.getId
  liftTermElabM do
    let info ← getConstInfo sourceName
    let tailInfo ← getConstInfo tailName
    unless info.levelParams.isEmpty && tailInfo.levelParams.isEmpty do
      throwError "expected monomorphic source and tail"
    let some original := info.value? | throwError "source has no definition"
    unless (original.find? (·.isConstOf tailName)).isSome do
      throwError "tail does not occur in source"
    let value ← withLocalDeclD `tail tailInfo.type fun callback => do
      let replaced := original.replace fun e => if e.isConstOf tailName then some callback else none
      mkLambdaFVars #[callback] replaced
    let type ← inferType value
    addDecl (.defnDecl {
      name := targetName
      levelParams := []
      type := type
      value := ShareCommon.shareCommon value
      hints := .abbrev
      safety := .safe })
    let type ← mkEq (mkConst sourceName) (mkApp (mkConst targetName) (mkConst tailName))
    addDecl (.thmDecl {
      name := targetName.str "equation"
      levelParams := []
      type := type
      value := ← mkEqRefl (mkConst sourceName) })
