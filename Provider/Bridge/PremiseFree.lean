import Lean
open Lean Meta Elab Command

/-- `#premise_free new from old`: `old : ∀ xs (hs : Props), lhs = rhs` whose proof term mentions
no Prop binder and whose conclusion mentions no Prop binder. Declares
`theorem new : ∀ xs, lhs = rhs` with the SAME proof body, abstracted over the non-Prop binders
only. The kernel re-checks the new declaration; nothing is assumed. -/
elab "#premise_free " new:ident " from " old:ident : command => liftTermElabM do
  let info ← getConstInfo old.getId
  let v ← match info with
    | .thmInfo t => pure t.value
    | _ => throwError "not a theorem"
  lambdaTelescope v fun xs body => do
    forallBoundedTelescope info.type xs.size fun ys concl => do
      let concl := concl.replaceFVars ys xs
      let mut keep := #[]
      for x in xs do
        unless ← isProp (← inferType x) do keep := keep.push x
      let fvs := (Lean.collectFVars {} body).fvarSet
      let cfvs := (Lean.collectFVars {} concl).fvarSet
      for x in xs do
        if ← isProp (← inferType x) then
          if fvs.contains x.fvarId! || cfvs.contains x.fvarId! then
            throwError "Prop binder {← x.fvarId!.getUserName} is used"
      let ty ← mkForallFVars keep concl
      let val ← mkLambdaFVars keep body
      addDecl (.thmDecl { name := new.getId, levelParams := info.levelParams, type := ty, value := val })
      logInfo m!"{new.getId} : {ty}"

/-- `#premise_min new from old`: like `#premise_free`, but keeps the Prop binders that the proof
body actually uses (and drops the rest). The kernel re-checks the new declaration. -/
elab "#premise_min " new:ident " from " old:ident : command => liftTermElabM do
  let info ← getConstInfo old.getId
  let v ← match info with
    | .thmInfo t => pure t.value
    | _ => throwError "not a theorem"
  lambdaTelescope v fun xs body => do
    forallBoundedTelescope info.type xs.size fun ys concl => do
      let concl := concl.replaceFVars ys xs
      let fvs := (Lean.collectFVars {} body).fvarSet
      let mut keep := #[]
      for x in xs do
        if ← isProp (← inferType x) then
          if fvs.contains x.fvarId! then keep := keep.push x
        else keep := keep.push x
      let ty ← mkForallFVars keep concl
      let val ← mkLambdaFVars keep body
      addDecl (.thmDecl { name := new.getId, levelParams := info.levelParams, type := ty, value := val })
      logInfo m!"{new.getId} : {ty}"
