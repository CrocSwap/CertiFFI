import Lean

open Lean Elab Command

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000

namespace ReleaseProfile

private def dropForall (wanted : String) : Expr → Option Expr
  | .forallE n ty body info =>
    if n.toString == wanted then
      if body.hasLooseBVar 0 then none else some (body.lowerLooseBVars 1 1)
    else
      (dropForall wanted body).map (.forallE n ty · info)
  | _ => none

private def dropLambda (wanted : String) : Expr → Option Expr
  | .lam n ty body info =>
    if n.toString == wanted then
      if body.hasLooseBVar 0 then none else some (body.lowerLooseBVars 1 1)
    else
      (dropLambda wanted body).map (.lam n ty · info)
  | _ => none

/-- Reuse the checked proof term after removing a syntactically unused premise.
    The resulting proof and entire reduced type are checked again by the kernel.
    A missing binder or a reference to it in a dependent type or proof fails. -/
syntax "drop_unused_premise " ident " from " ident " named " str : command

elab_rules : command
  | `(drop_unused_premise $result:ident from $original:ident named $binder:str) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo original
    let .thmInfo info ← getConstInfo name
      | throwErrorAt original "expected an imported theorem"
    let some type := dropForall binder.getString info.type
      | throwErrorAt binder "binder is missing or used in the theorem type"
    let some value := dropLambda binder.getString info.value
      | throwErrorAt binder "binder is missing or used in the proof value"
    liftCoreM <| addDecl (.thmDecl {
      name := (← getCurrNamespace) ++ result.getId
      levelParams := info.levelParams
      type
      value
    })

end ReleaseProfile
