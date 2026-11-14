import Std.Data.HashSet
import CryptoMem.Tac2
open Lean Meta Elab Tactic

/-- Collect the distinct ite/dite conditions of an expression (DAG walk with a visited set). -/
partial def collectConds (e : Expr) (st : Std.HashSet Expr × Array Expr) : Std.HashSet Expr × Array Expr :=
  if st.1.contains e then st else
  let st := (st.1.insert e, st.2)
  let st := if (e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5) then
      (let c := e.getArg! 1; if st.2.contains c then st else (st.1, st.2.push c)) else st
  match e with
  | .app f a => collectConds a (collectConds f st)
  | .lam _ t b _ => collectConds b (collectConds t st)
  | .forallE _ t b _ => collectConds b (collectConds t st)
  | .letE _ t v b _ => collectConds b (collectConds v (collectConds t st))
  | .mdata _ b => collectConds b st
  | .proj _ _ b => collectConds b st
  | _ => st

/-- show_conds: diagnostic; logs every distinct ite/dite condition of the goal (armcert-crypto). -/
elab "show_conds" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let (_, cs) := collectConds t ({}, #[])
  logInfo m!"{cs.size} distinct conditions"
  for c in cs do
    logInfo m!"COND: {c}"

/-- show_match h: diagnostic; prints (explicitly) the lhs of hypothesis h and the first goal subterm
with the same head symbol and argument count (armcert-crypto). -/
elab "show_match " h:ident : tactic => withMainContext do
  let d ← getLocalDeclFromUserName h.getId
  let ty ← instantiateMVars d.type
  let some (_, l, _) := ty.eq? | throwError "not an eq"
  let t ← instantiateMVars (← getMainTarget)
  let hd := l.getAppFn
  let n := l.getAppNumArgs
  let la0 := l.getAppArgs
  let same (e : Expr) : Bool := e.getAppFn == hd && e.getAppNumArgs == n && e != l &&
    (n < 6 || e.getAppArgs[n-2]! == la0[n-2]!)
  match t.find? same with
  | some e =>
    logInfo m!"LHS: {l}"
    logInfo m!"GOAL: {e}"
    logInfo m!"defeq(reducible)? {← withReducible (isDefEq l e)}  defeq(default)? {← isDefEq l e}"
    let la := l.getAppArgs; let ea := e.getAppArgs
    for i in [0:n] do
      if la[i]! != ea[i]! then
        logInfo m!"arg {i} differs:\n  {la[i]!}\n  vs\n  {ea[i]!}"
  | none => logInfo m!"no differing occurrence of head {hd}"

/-- Like collectConds, but skips instance-implicit and proof arguments (MetaM). -/
partial def collectConds2 (e : Expr) (st : Std.HashSet Expr × Array Expr) : MetaM (Std.HashSet Expr × Array Expr) := do
  if st.1.contains e then return st
  let mut st := (st.1.insert e, st.2)
  if (e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5) then
    let c := e.getArg! 1
    if !st.2.contains c then st := (st.1, st.2.push c)
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    st ← collectConds2 f st
    let info ← try (some <$> getFunInfoNArgs f args.size) catch _ => pure none
    for i in [0:args.size] do
      let a := args[i]!
      let skip := match info with
        | some fi => if h : i < fi.paramInfo.size then fi.paramInfo[i].isInstImplicit || fi.paramInfo[i].isProp else false
        | none => false
      if !skip then st ← collectConds2 a st
    return st
  | .lam _ t b _ => collectConds2 b (← collectConds2 t st)
  | .letE _ t v b _ => collectConds2 b (← collectConds2 v (← collectConds2 t st))
  | .mdata _ b => collectConds2 b st
  | .proj _ _ b => collectConds2 b st
  | _ => return st

elab "show_conds2" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let (_, cs) ← collectConds2 t ({}, #[])
  logInfo m!"{cs.size} distinct computational conditions"
  for c in cs do
    logInfo m!"COND2: {c}"

/-- abst_rw h (h : lhs = rhs, lhs an application): rewrite EVERY subterm of the goal that has the
same head constant as lhs and the same non-instance, non-proof arguments (so instance paths and bound
proofs may differ), by abstracting them all into one variable, checking the motive, changing the goal
by defeq, and rewriting with congrArg (kernel-checked) (armcert-crypto). -/
elab "abst_rw " h:ident : tactic => withMainContext do
  let d ← getLocalDeclFromUserName h.getId
  let ty ← instantiateMVars d.type
  let some (α, l, r) := ty.eq? | throwError "abst_rw: not an equation"
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let fn := l.getAppFn
  let n := l.getAppNumArgs
  let finfo ← getFunInfoNArgs fn n
  let keyIdx := (List.range n).filter fun i =>
    if h : i < finfo.paramInfo.size then !(finfo.paramInfo[i].isInstImplicit || finfo.paramInfo[i].isProp) else true
  let la := l.getAppArgs
  let isOcc (e : Expr) : Bool :=
    e.getAppFn == fn && e.getAppNumArgs == n &&
      keyIdx.all fun i => e.getAppArgs[i]! == la[i]!
  let motive ← withLocalDeclD `z α fun z => do
    mkLambdaFVars #[z] (t.replace fun x => if isOcc x then some z else none)
  if !(← isTypeCorrect motive) then throwError "abst_rw: motive not type-correct"
  let t1 := (mkApp motive l).headBeta
  let g1 ← g.replaceTargetDefEq t1
  let newT := (mkApp motive r).headBeta
  replaceMainGoal [← g1.replaceTargetEq newT (← mkCongrArg motive d.toExpr)]

/-- Path (head constant, argument index) from the root to the first subterm satisfying p. -/
partial def findPath (p : Expr → Bool) (e : Expr) (vis : IO.Ref (Std.HashSet Expr)) : IO (Option (List String)) := do
  if (← vis.get).contains e then return none
  vis.modify (·.insert e)
  if p e then return some []
  match e with
  | .app .. =>
    let f := e.getAppFn; let args := e.getAppArgs
    let nm := match f with | .const n _ => n.toString | .fvar _ => "fvar" | .lam .. => "lam" | _ => "?"
    for i in [0:args.size] do
      if let some r ← findPath p args[i]! vis then return some (s!"{nm}#{i}" :: r)
    if let some r ← findPath p f vis then return some ("fn" :: r)
    return none
  | .lam _ t b _ =>
    if let some r ← findPath p t vis then return some ("lamTy" :: r)
    if let some r ← findPath p b vis then return some ("lamBody" :: r)
    return none
  | .forallE _ t b _ =>
    if let some r ← findPath p t vis then return some ("piTy" :: r)
    if let some r ← findPath p b vis then return some ("piBody" :: r)
    return none
  | .letE _ t v b _ =>
    if let some r ← findPath p v vis then return some ("letV" :: r)
    if let some r ← findPath p b vis then return some ("letB" :: r)
    return none
  | .mdata _ b => findPath p b vis
  | .proj _ i b => do if let some r ← findPath p b vis then return some (s!"proj{i}" :: r) else return none
  | _ => return none

elab "show_path " h:ident : tactic => withMainContext do
  let d ← getLocalDeclFromUserName h.getId
  let ty ← instantiateMVars d.type
  let some (_, l, _) := ty.eq? | throwError "not an eq"
  let t ← instantiateMVars (← getMainTarget)
  let n := l.getAppNumArgs; let la := l.getAppArgs
  let p := fun (e : Expr) => e.getAppFn == l.getAppFn && e.getAppNumArgs == n && e != l &&
    e.getAppArgs[n-2]! == la[n-2]! && e.getAppArgs[n-3]! == la[n-3]!
  let vis ← IO.mkRef ({} : Std.HashSet Expr)
  match ← findPath p t vis with
  | some path => logInfo m!"PATH: {path}"
  | none => logInfo m!"no occurrence"

/-- name_whole f n as x: generalize the first closed n-ary application of the constant f (the whole
application, syntactic occurrences only) into x, recording hx : app = x. Implemented without
kabstract/isDefEq: the motive is checked for type-correctness instead (armcert-crypto). -/
elab "name_whole " f:ident n:num " as " x:ident : tactic => withMainContext do
  let fn ← realizeGlobalConstNoOverloadWithInfo f
  let n := n.getNat
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some e := t.find? (fun e => e.isAppOf fn && e.getAppNumArgs == n && !e.hasLooseBVars)
    | throwError "name_whole: no closed {n}-ary application of {fn}"
  let α ← inferType e
  let newGoalTy ← withLocalDeclD x.getId α fun xv => do
    let body := t.replace fun y => if y == e then some xv else none
    withLocalDeclD (x.getId.appendBefore "h") (← mkEq e xv) fun hv => do
      mkForallFVars #[xv, hv] body
  if !(← isTypeCorrect newGoalTy) then throwError "name_whole: generalized goal not type-correct"
  let ng ← mkFreshExprSyntheticOpaqueMVar newGoalTy
  g.assign (mkApp2 ng e (← mkEqRefl e))
  let (_, ng2) ← ng.mvarId!.introNP 2
  replaceMainGoal [ng2]
