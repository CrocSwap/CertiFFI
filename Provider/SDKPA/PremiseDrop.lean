import Lean
open Lean Meta Elab Command

/-! a design decision (additive): `#premise_drop new from old drop h` — like Bridge.PremiseFree's
`#premise_min`, but drops ONLY the Prop binder named `h`, and fails if the proof body or the
conclusion uses it. All other binders (and their order) are kept, so call sites change only by
removing that one argument. The kernel re-checks the new declaration; nothing is assumed. -/
elab "#premise_drop " new:ident " from " old:ident " drop " h:ident : command => liftTermElabM do
  let info ← getConstInfo old.getId
  let v ← match info with
    | .thmInfo t => pure t.value
    | _ => throwError "not a theorem"
  lambdaTelescope v fun xs body => do
    forallBoundedTelescope info.type xs.size fun ys concl => do
      let concl := concl.replaceFVars ys xs
      let fvs := (Lean.collectFVars {} body).fvarSet
      let cfvs := (Lean.collectFVars {} concl).fvarSet
      let mut keep := #[]
      let mut dropped : Nat := 0
      for x in xs do
        if (← x.fvarId!.getUserName) == h.getId then
          unless ← isProp (← inferType x) do throwError "binder {h.getId} is not a Prop"
          if fvs.contains x.fvarId! || cfvs.contains x.fvarId! then
            throwError "binder {h.getId} is used"
          dropped := dropped + 1
        else keep := keep.push x
      unless dropped == 1 do throwError "binder {h.getId} found {dropped} times"
      let ty ← mkForallFVars keep concl
      let val ← mkLambdaFVars keep body
      addDecl (.thmDecl { name := new.getId, levelParams := info.levelParams, type := ty, value := val })
      logInfo m!"{new.getId} : {ty}"
