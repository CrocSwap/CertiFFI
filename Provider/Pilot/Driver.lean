import Pilot.LoopFrame
import Pilot.ExceptLoop
import Pilot.InvariantLoop
import Lean.Meta.WrapInstance
import Lean.Meta.Tactic.Cases
import Pilot.DemandedProjection
import Pilot.StepCert
import Pilot.StepRuntime
import Pilot.BitFieldSummary
import Init.Omega
import Lean.Util.ShareCommon
import Pilot.FiniteControl
open Lean Meta Elab Command Term
namespace Stepping
initialize summaryExt : SimpExtension ←
  registerSimpAttr `step_summary "Kernel-checked callee summaries for the stepping evaluator"
initialize compositionalCalleesRef : IO.Ref (Array Name) ← IO.mkRef #[]
structure EvalResult where
  expr : Expr
  proof : Expr
structure Context where
  simp : Simp.Context
  procs : Simp.SimprocsArray
  summaries : SimpTheorems
  opaqueNames : Array Name := #[]
  compositionalNative : Bool := false
structure Stats where
  steps : Nat := 0
  cache : Std.HashMap Expr EvalResult := {}
  cacheHits : Nat := 0
  deriving Inhabited
abbrev EvalM := ReaderT Context (StateRefT Stats MetaM)

def chain (p q : Expr) : MetaM Expr := do
  if (← IO.getEnv "EVAL_TRACE").isSome then
    IO.FS.writeFile "logs/driver-chain.txt" s!"enter left={p.getAppFn.constName?} right={q.getAppFn.constName?}"
  let result ← Lean.Meta.mkEqTrans p q
  if (← IO.getEnv "EVAL_TRACE").isSome then
    IO.FS.writeFile "logs/driver-chain.txt" "returned"
  return result

def isState (ty : Expr) : MetaM Bool := do
  return (← whnf ty).isAppOf ``Sail.ConcurrencyInterfaceV1.SequentialState

def certified (e out pf : Expr) : EvalM EvalResult := do
  let r ← StepEval.certify e { expr := out, proof? := some pf }
  return ⟨out, r.proof?.getD pf⟩

/-- Structural lifting composes certificates already checked at their redexes. -/
def compose (_e out pf : Expr) : EvalM EvalResult := return ⟨out, pf⟩

/-- Keep branch joins shared before abstracting their local assumptions. -/
def sharedCompose (_e out pf : Expr) : EvalM EvalResult := do
  IO.FS.writeFile "logs/driver-sharing.txt" "sharing compose enter"
  let (out, pf) := ShareCommon.shareCommon (out, pf)
  IO.FS.writeFile "logs/driver-sharing.txt" "sharing compose returned"
  return ⟨out, pf⟩

def refl (e : Expr) : EvalM EvalResult := return ⟨e, ← mkEqRefl e⟩

/-- Specialize delayed record fields using premises, without evaluating data. -/
def rewriteNativeProfile (e : Expr) : MetaM Simp.Result := do
  let mut thms : SimpTheorems := {}
  for d in (← getLCtx) do
    unless d.isImplementationDetail do
      if ← isProp d.type then
        thms ← thms.add (.fvar d.fvarId) #[] d.toExpr
        let normalized ← StepEval.normalizeLookupFact d.toExpr
        if normalized != d.toExpr then
          thms ← thms.add (.other (← mkFreshUserName `lookupFact)) #[] normalized
  let ctx ← Simp.mkContext {
    maxSteps := 20000, dsimp := false, beta := false, zeta := false,
    iota := false, proj := false, decide := false }
    #[thms] (← getSimpCongrTheorems)
  let methods := Simp.mkDefaultMethodsCore #[]
  let pre : Simp.Simproc := fun value => do
    let head := value.getAppFn
    if head.isConstOf ``Sail.ConcurrencyInterfaceV1.ChoiceSource.chooseAt then
      return .done {expr := value}
    if head.isConstOf ``GetElem.getElem && value.getAppNumArgs == 8 &&
        (value.getAppArgs[6]!.hasFVar || value.getAppArgs[6]!.hasLooseBVars) then
      return .done {expr := value}
    if let .const n _ := head then
      if let .ctorInfo ci ← getConstInfo n then
        if ci.induct == ``Sail.ConcurrencyInterfaceV1.SequentialState ||
            ci.induct == ``Sail.ConcurrencyInterfaceV1.ChoiceLabel || ci.induct == ``Fin then
          return .done {expr := value}
    methods.pre value
  let (r, _) ← Simp.main e ctx (methods := {methods with pre})
  StepEval.certify e r

def normalizeState (e : Expr) : EvalM EvalResult := do
  -- Keep the conditional visible to projectConditional, which projects each
  -- needed field before reducing branches. whnf would hide it in Bool.rec.
  if e.getAppFn.isConstOf ``ite || e.getAppFn.isConstOf ``dite then
    return ← refl e
  let out ← withTransparency .all <| whnf e
  if out == e then return ← refl e
  let pf ← mkExpectedTypeHint (← mkEqRefl e) (← mkEq e out)
  certified e out pf

/-- Only a returned value is simplified; no pending monadic continuation is in scope. -/
partial def normalizeValue (e : Expr) : EvalM EvalResult := do
  let ty ← inferType e
  if (← isState ty) || (← whnf ty).isForall then return ← refl e
  let c ← read
  unless ty.isAppOf ``BitVec do
    let reducedTy ← whnf ty
    if let .const n _ := reducedTy.getAppFn then
      let dataType : Bool ← if n == ``Nat || n == ``Int || n == ``Bool || n == ``Fin then pure false else do
        if (getStructureInfo? (← getEnv) n).isSome then pure true
        else
          match ← getConstInfo n with
          | .inductInfo info => info.ctors.anyM fun ctor => return (← getConstInfoCtor ctor).numFields > 0
          | _ => pure false
      if dataType then
        -- Returned records are data. Normalize the fields a caller demands,
        -- rather than spending one paused simp pass on every unused field.
        IO.FS.writeFile "logs/driver-value-phase.txt" s!"record projection enter type={n} head={e.getAppFn.constName?}"
        let r ← StepEval.recordProjectionSteps e
        IO.FS.writeFile "logs/driver-value-phase.txt" s!"record projection returned type={n} head={r.expr.getAppFn.constName?}"
        let mut cur := r.expr
        let mut pf := r.proof?.getD (← mkEqRefl e)
        let thms := c.simp.simpTheorems[0]!
        -- Root canonicalization can expose a local fact (e.g. get? -> [i]?).
        -- Reach the root fixed point without traversing record/Option payloads.
        for _ in [0:32] do
          let (root?, _) ← Simp.SimpM.run c.simp {} (Simp.mkDefaultMethodsCore c.procs) do
            Simp.rewrite? cur thms.post thms.erased "record_profile" false
          let some root := root? | do
            -- Only lookup inputs are demanded here. In particular, never walk
            -- an Option constructor's payload or the contents of a map.
            unless cur.getAppFn.isConstOf ``GetElem?.getElem? do return ⟨cur, pf⟩
            let args := cur.getAppArgs
            let mut fnTy ← inferType cur.getAppFn
            let mut changed := false
            for i in [0:args.size] do
              let a := args[i]!
              let .forallE _ aty body _ ← whnf fnTy | break
              fnTy := body.instantiate1 a
              if i + 2 < args.size then continue
              if body.hasLooseBVar 0 then continue
              let aty ← whnf aty
              if aty.isSort || (← isProp a) then continue
              let scalar := aty.isConstOf ``Nat || aty.isConstOf ``Int ||
                aty.isConstOf ``Bool || aty.isAppOf ``BitVec || aty.isAppOf ``Fin
              let ar ← if scalar then normalizeValue a else do
                let r ← StepEval.recordProjectionSteps a
                pure ⟨r.expr, r.proof?.getD (← mkEqRefl a)⟩
              if ar.expr == a then continue
              let f ← withLocalDeclD `lookupInput aty fun v =>
                mkLambdaFVars #[v] (mkAppN cur.getAppFn (args.set! i v))
              pf ← chain pf (← mkCongrArg f ar.proof)
              cur := mkAppN cur.getAppFn (args.set! i ar.expr)
              changed := true
              break
            if !changed then return ⟨cur, pf⟩
            continue
          if root.expr == cur then return ⟨cur, pf⟩
          let rp ← match root.proof? with
            | some p => pure p
            | none => mkExpectedTypeHint (← mkEqRefl cur) (← mkEq cur root.expr)
          pf ← chain pf rp
          cur := root.expr
        throwError "record root normalization did not reach a fixpoint"
  let mut cur := e
  let mut pf ← mkEqRefl e
  for _ in [0:32] do
    -- Keep symbolic joins available for projection and continuation sharing.
    -- Reducing their decidable instance here hides them inside Bool.rec.
    let as := cur.getAppArgs
    if (cur.getAppFn.isConstOf ``ite || cur.getAppFn.isConstOf ``dite) && as.size == 5 &&
        (as[1]!.hasFVar || as[1]!.hasLooseBVars) then
      return ← certified e cur pf
    IO.FS.writeFile "logs/driver-value-phase.txt" s!"scalar simp enter head={cur.getAppFn.constName?}"
    let (r, _) ← StepEval.simpSteps cur c.simp c.procs none (some StepEval.DemandedProjection.normalize?)
    IO.FS.writeFile "logs/driver-value-phase.txt" s!"scalar simp returned head={r.expr.getAppFn.constName?}"
    let p ← match r.proof? with
      | some p => pure p
      | none => mkExpectedTypeHint (← mkEqRefl cur) (← mkEq cur r.expr)
    pf ← chain pf p
    IO.FS.writeFile "logs/driver-value-phase.txt" "scalar proof chain returned"
    if cur == r.expr then return ← certified e cur pf
    cur := r.expr
  IO.FS.writeFile "logs/value-fixpoint-type.txt"
    s!"type={← ppExpr ty} originalHead={e.getAppFn.constName?} finalHead={cur.getAppFn.constName?}\n"
  throwError "value normalization did not reach a fixpoint"

def scalarType (ty : Expr) : MetaM Bool := do
  if ty.isConstOf ``Bool || ty.isConstOf ``Nat || ty.isConstOf ``Int || ty.isAppOf ``BitVec then
    return true
  let .const n _ := ty.getAppFn | return false
  let .inductInfo info ← getConstInfo n | return false
  for ctor in info.ctors do
    let ci ← getConstInfoCtor ctor
    if ci.numFields != 0 then return false
  return true

def prepareInputs (e : Expr) : EvalM (Option EvalResult) := do
  let .const n _ := e.getAppFn | return none
  unless (`ArmFull.Functions).isPrefixOf n do return none
  let args := e.getAppArgs
  let mut fnTy ← inferType e.getAppFn
  for i in [0:args.size] do
    let a := args[i]!
    let .forallE _ ty b _ ← whnf fnTy | return none
    fnTy := b.instantiate1 a
    if b.hasLooseBVar 0 || !(← scalarType ty) then continue
    let r ← normalizeValue a
    if r.expr == a then continue
    let f ← withLocalDeclD `input ty fun v =>
      mkLambdaFVars #[v] (mkAppN e.getAppFn (args.set! i v))
    return some ⟨mkAppN e.getAppFn (args.set! i r.expr), ← mkCongrArg f r.proof⟩
  return none

def align (e pf : Expr) : MetaM (Expr × Expr) := do
  IO.FS.writeFile "logs/driver-align.txt" s!"infer enter {e.getAppFn.constName?} proof={pf.getAppFn.constName?}"
  let some (_, lhs, rhs) := (← inferType pf).consumeMData.eq? | throwError "expected an equation"
  IO.FS.writeFile "logs/driver-align.txt" s!"defeq enter {e.getAppFn.constName?}"
  unless ← isDefEq lhs e do throwError "driver equation does not start at input"
  IO.FS.writeFile "logs/driver-align.txt" "instantiate enter"
  let result := (← instantiateMVars rhs, ← instantiateMVars pf)
  IO.FS.writeFile "logs/driver-align.txt" "returned"
  return result

/-- A proved native result needs no second traversal before a bind consumes it. -/
partial def isNativeResultTree (e : Expr) : Bool :=
  let e := e.consumeMData.headBeta
  let f := e.getAppFn
  let as := e.getAppArgs
  if f.isConstOf ``EStateM.Result.ok || f.isConstOf ``EStateM.Result.error then true
  else if (f.isConstOf ``ite || f.isConstOf ``dite) && as.size == 5 then
    let branch (v : Expr) := if f.isConstOf ``dite then
      if v.isLambda then isNativeResultTree v.bindingBody! else false
      else isNativeResultTree v
    branch as[3]! && branch as[4]!
  else false

/-- Count distinct syntax nodes without expanding shared subexpressions. -/
partial def collectNativeNodes (e : Expr) : StateM (Std.HashSet Expr) Unit := do
  if (← get).contains e then return
  modify (·.insert e)
  match e with
  | .forallE _ d b _ | .lam _ d b _ => collectNativeNodes d; collectNativeNodes b
  | .mdata _ b | .proj _ _ b => collectNativeNodes b
  | .letE _ t v b _ => collectNativeNodes t; collectNativeNodes v; collectNativeNodes b
  | .app f a => collectNativeNodes f; collectNativeNodes a
  | _ => pure ()

def delta (e : Expr) : EvalM EvalResult := do
  let r? ← StepEval.deltaBeforeStateCore e
  if let some r := r? then
    let some pf := r.proof? | throwError "delta missing proof"
    return ⟨r.expr, pf⟩
  throwError "cannot unfold computation {e.getAppFn}"

def dependentConditional (e : Expr) : MetaM (Option EvalResult) := do
  unless e.getAppFn.isConstOf ``dite do return none
  let args := e.getAppArgs
  if args.size < 5 then return none
  let dec := args[2]!
  if dec.hasFVar || dec.hasMVar || dec.hasLooseBVars then return none
  let yesTy ← mkArrow args[1]! args[0]!
  let noTy ← mkArrow (mkNot args[1]!) args[0]!
  let (out, pf) ← withLocalDeclD `yesBranch yesTy fun y => do
    withLocalDeclD `noBranch noTy fun n => do
      let generic := mkAppN e.getAppFn ((args.extract 0 5).set! 3 y |>.set! 4 n)
      let out ← withTransparency .all <| whnf generic
      let r ← StepEval.certify generic { expr := out }
      let some pf := r.proof? | throwError "dependent conditional unchanged"
      return (out.replaceFVars #[y,n] #[args[3]!,args[4]!],
        pf.replaceFVars #[y,n] #[args[3]!,args[4]!])
  let mut out := out
  let mut pf := pf
  for a in args.extract 5 args.size do
    pf ← mkCongrFun pf a
    out := mkApp out a
  return some ⟨out, pf⟩

/-- Decide only what follows from the current hypotheses, with a proof-producing solver. -/
def arithmeticDecision (p : Expr) : MetaM (Option (Bool × Expr)) := do
  -- Omega is optional proof search. Avoid feeding it an execution-history DAG;
  -- keep the existing simplification/branch path for such conditions.
  let mut pending := #[p]
  let mut seen : Std.HashSet Expr := {}
  while !pending.isEmpty do
    let value := pending.back!
    pending := pending.pop
    if seen.contains value then continue
    seen := seen.insert value
    if seen.size > 512 then
      IO.FS.writeFile "logs/driver-arith-budget.txt" "skip: condition exceeds 512 distinct syntax nodes"
      return none
    match value with
    | .app f a => pending := pending.push f |>.push a
    | .forallE _ d b _ | .lam _ d b _ => pending := pending.push d |>.push b
    | .letE _ t v b _ => pending := pending.push t |>.push v |>.push b
    | .mdata _ b | .proj _ _ b => pending := pending.push b
    | _ => pure ()
  let prove (negative : Bool) : MetaM Expr := do
    let assumption := if negative then p else mkNot p
    withLocalDeclD `arithmeticAssumption assumption fun h => do
      let mut facts := [h]
      for decl in (← getLCtx) do
        unless decl.isImplementationDetail do
          if ← isProp decl.type then facts := decl.toExpr :: facts
      let goal ← mkFreshExprSyntheticOpaqueMVar (mkConst ``False)
      Lean.Elab.Tactic.Omega.omega facts goal.mvarId! {}
      let prf ← instantiateMVars goal
      if prf.hasMVar then throwError "arithmetic proof incomplete"
      let prf ← mkLambdaFVars #[h] prf
      if negative then pure prf else mkAppM ``Classical.byContradiction #[prf]
  for negative in [false, true] do
    IO.FS.writeFile "logs/driver-arith.txt" s!"enter negative={negative} outerHB={← Lean.getMaxHeartbeats}"
    let result? ← tryCatchRuntimeEx (do
      let prf ← withCurrHeartbeats <|
        withTheReader Core.Context (fun c => {c with maxHeartbeats := 1000000}) <|
          prove negative
      pure (some prf))
      (fun _ => pure none)
    IO.FS.writeFile "logs/driver-arith.txt" s!"returned negative={negative} success={result?.isSome} outerHB={← Lean.getMaxHeartbeats}"
    if let some prf := result? then
      recordExtraModUse (isMeta := false) `Init.Omega
      let decisionType := if negative then mkNot p else p
      let eqProof ← mkAppM ``eq_true #[prf]
      let r ← StepEval.certify decisionType {expr := mkConst ``True, proof? := some eqProof}
      let prf ← mkOfEqTrue r.proof?.get!
      return some (!negative, prf)
  return none

def conditional (e : Expr) : EvalM (Option EvalResult) := do
  unless e.getAppFn.isConstOf ``ite || e.getAppFn.isConstOf ``dite do return none
  let args := e.getAppArgs
  if args.size < 5 then return none
  if let some r ← StepEval.closedIte e then
    return some ⟨r.expr, r.proof?.get!⟩
  if let some r ← dependentConditional e then return some r
  if let some (yes, conditionProof) ← arithmeticDecision args[1]! then
    let lemma := if e.getAppFn.isConstOf ``dite then
        if yes then ``dite_eq_left else ``dite_eq_right
      else if yes then ``ite_eq_left else ``ite_eq_right
    let level ← getLevel args[0]!
    let pf := mkAppN (mkConst lemma [level])
      #[args[1]!,args[2]!,conditionProof,args[0]!,args[3]!,args[4]!]
    let some (_, _, out) := (← inferType pf).consumeMData.eq? | throwError "conditional arithmetic proof malformed"
    let mut pf := pf
    let mut out := out
    for a in args.extract 5 args.size do
      pf ← mkCongrFun pf a
      out := mkApp out a
    return some ⟨out, pf⟩
  let c ← read
  let yesTy ← if e.getAppFn.isConstOf ``dite then mkArrow args[1]! args[0]! else pure args[0]!
  let noTy ← if e.getAppFn.isConstOf ``dite then mkArrow (mkNot args[1]!) args[0]! else pure args[0]!
  let result? ← tryCatchRuntimeEx (do
    pure (some (← withLocalDeclD `yesBranch yesTy fun y => do
    withLocalDeclD `noBranch noTy fun n => do
     StepEval.withOpaque #[y,n] do
      let generic := mkAppN e.getAppFn ((args.extract 0 5).set! 3 y |>.set! 4 n)
      let mut cur := generic
      let mut pf ← mkEqRefl generic
      for _ in [0:32] do
        IO.FS.writeFile "logs/driver-phase.txt" "conditional: simp enter"
        let (r, _) ← withCurrHeartbeats <|
          withTheReader Core.Context (fun ctx => {ctx with maxHeartbeats := 2000000}) <|
            withOptions (fun o => o.set `maxHeartbeats (2000 : Nat)) <|
              StepEval.simpSteps cur c.simp c.procs none
        IO.FS.writeFile "logs/driver-phase.txt" "conditional: simp returned"
        let p ← match r.proof? with
          | some p => pure p
          | none => mkExpectedTypeHint (← mkEqRefl cur) (← mkEq cur r.expr)
        pf ← chain pf p
        if r.expr == cur then break
        cur := r.expr
      let used := (collectFVars {} cur).fvarSet
      if used.contains y.fvarId! && used.contains n.fvarId! &&
          !cur.getAppFn.isConstOf ``ite && !cur.getAppFn.isConstOf ``dite then
        -- An unresolved decision must remain a branch join, rather than a
        -- reduced Bool/Decidable recursor which hides both alternatives.
        cur := generic
        pf ← mkEqRefl generic
      let r ← StepEval.certify generic { expr := cur, proof? := some pf }
      IO.FS.writeFile "logs/driver-phase.txt" "conditional: certified"
      let finalProof := r.proof?.getD pf
      return (cur.replaceFVars #[y,n] #[args[3]!,args[4]!],
        finalProof.replaceFVars #[y,n] #[args[3]!,args[4]!])) ))
    (fun ex => do
      unless ex.isMaxHeartbeat do throw ex
      IO.FS.withFile "logs/driver-fallback.txt" .append fun h =>
        h.putStrLn "Conditional simplification budget exhausted; retaining original condition for exhaustive split."
      pure none)
  let some (out, pf) := result? | return none
  let mut out := out
  let mut pf := pf
  for a in args.extract 5 args.size do
    pf ← mkCongrFun pf a
    out := mkApp out a
  if out == e then return none
  return some ⟨out, pf⟩

/-- Rewrite a dependent recursor major on the fully applied result spine.
Lean's checked congruence theorem transports proof-only dependent arguments;
ordinary congrArg is valid only when the recursor's motive is constant. -/
def rewriteDependentMajor (e : Expr) (majorIndex : Nat)
    (normalized : EvalResult) : MetaM EvalResult := do
  let args := e.getAppArgs
  let .const name _ := e.getAppFn | throwError "recursor head is not constant"
  let .recInfo info ← getConstInfo name | throwError "head is not a recursor"
  let firstMinor := info.getFirstMinorIdx
  let rec abstract (index : Nat) (current xs actual : Array Expr) : MetaM EvalResult := do
    if index < firstMinor + info.numMinors then
      let input := current[index]!
      withLocalDeclD `recursorMinor (← inferType input) fun v =>
        abstract (index + 1) (current.set! index v) (xs.push v) (actual.push input)
    else
      let f := mkAppN e.getAppFn (current.extract 0 majorIndex)
      let spine := current.extract majorIndex current.size
      let some congr ← mkCongrSimp? f (maxArgs? := some spine.size)
        | throwError "dependent recursor has no result-spine congruence theorem"
      unless congr.argKinds.size == spine.size && congr.argKinds[0]! == .eq do
        throwError "dependent recursor major cannot be rewritten by result-spine congruence"
      -- Check the generic theorem with opaque minors and abstract spine inputs.
      -- Applying it later is structural composition, without rechecking an
      -- entire pending monadic continuation or concrete data/state expression.
      let checked ← forallTelescope congr.type fun inputs conclusion => do
        let some (_, lhs, rhs) := conclusion.eq?
          | throwError "dependent congruence conclusion is not an equality"
        let proof := mkAppN congr.proof inputs
        let result ← StepEval.certify lhs {expr := rhs, proof? := some proof}
        mkLambdaFVars inputs result.proof?.get!
      let mut inputs := #[]
      for i in [0:spine.size] do
        let original := spine[i]!
        match congr.argKinds[i]! with
        | .fixed => inputs := inputs.push original
        | .eq =>
          let next := if i == 0 then normalized.expr else original
          let proof ← if i == 0 then pure normalized.proof else mkEqRefl original
          inputs := inputs ++ #[original, next, proof]
        | .cast => inputs := inputs.push original
        | .fixedNoParam => pure ()
        | _ => throwError "unsupported dependent recursor congruence argument"
      let proof := mkAppN checked inputs
      let some (_, _, next) := (← inferType proof).eq?
        | throwError "dependent result-spine proof has no equality"
      return ⟨next.replaceFVars xs actual, proof.replaceFVars xs actual⟩
  abstract firstMinor args #[] #[]

/-- Nonrecursive structure eta expansion, adapted from Lean4.35
Lean.Meta.WrapInstance.etaStructExpand? (Apache2.0). It changes no data and
is validated by the same kernel-checked definitional-equality certificates. -/
def constructorEta? (e : Expr) : MetaM (Option Expr) := do
  if (← isConstructorApp? e).isSome then return none
  let ty ← instantiateMVars (← whnf (← inferType e))
  let .const name levels := ty.getAppFn | return none
  let env ← getEnv
  unless isStructure env name && isNonRecStructure env name do return none
  if ← isProp ty then return none
  let info ← getConstInfoInduct name
  let some ctor := info.ctors.head? | return none
  let ci ← getConstInfoCtor ctor
  let params := ty.getAppArgs.shrink ci.numParams
  let structureInfo := getStructureInfo? env name
  let mut result := mkAppN (mkConst ctor levels) params
  for field in [0:ci.numFields] do
    let value := match structureInfo.bind (·.getProjFn? field) with
      | some projection => mkApp (mkAppN (mkConst projection levels) params) e
      | none => mkProj name field e
    result := mkApp result value
  return some result

structure FrameLens where
  project : Expr
  restore : Expr
  selfProof : Expr

/-- The actual generated native state's register-file field is separate from
choice counters, memory and events. The setter is a kernel-checked record update. -/
def nativeRegsLens? (state : Expr) : MetaM (Option FrameLens) := do
  let ty ← inferType state
  unless ← isState ty do return none
  withLocalDeclD `frameState ty fun current => do
    let some expanded ← constructorEta? current | return none
    let .const ctor _ := expanded.getAppFn | return none
    let info ← getConstInfoCtor ctor
    let fields := expanded.getAppArgs
    let registers := fields[info.numParams]!
    let project ← mkLambdaFVars #[current] registers
    let restore ← withLocalDeclD `frameRegisters (← inferType registers) fun replacement =>
      mkLambdaFVars #[replacement, current]
        (mkAppN expanded.getAppFn (fields.set! info.numParams replacement))
    let selfType ← mkEq (mkApp2 restore (mkApp project current) current) current
    let self ← mkExpectedTypeHint (← mkEqRefl current) selfType
    return some ⟨project, restore, ← mkLambdaFVars #[current] self⟩

/-- Normalize the demanded register projection, retaining every other state field. -/
def normalizeRegisters (state : Expr) : MetaM EvalResult := do
  let some lens ← nativeRegsLens? state | return ⟨state, ← mkEqRefl state⟩
  let projected := mkApp lens.project state
  let normalized ← StepEval.recordProjectionSteps projected
  if normalized.expr == projected then return ⟨state, ← mkEqRefl state⟩
  let proof := normalized.proof?.getD (← mkExpectedTypeHint
    (← mkEqRefl projected) (← mkEq projected normalized.expr))
  let setter ← withLocalDeclD `registerValue (← inferType normalized.expr) fun value =>
    mkLambdaFVars #[value] (mkApp2 lens.restore value state)
  let restored := mkApp2 lens.restore normalized.expr state
  let equality ← mkEqTrans (← mkEqSymm (mkApp lens.selfProof state))
    (← mkCongrArg setter proof)
  let result ← StepEval.certify state {expr := restored, proof? := some equality}
  return ⟨result.expr, result.proof?.getD equality⟩

/-- Optional proof search using exactly the current local facts. The syntax
budget bounds search only; failure retains the ordinary evaluator path. -/
def frameLocalEq? (left right : Expr) : MetaM (Option Expr) := do
  let target ← mkEq left right
  let mut pending := #[target]
  let mut seen : Std.HashSet Expr := {}
  while !pending.isEmpty do
    let e := pending.back!
    pending := pending.pop
    if !seen.contains e then
      seen := seen.insert e
      if seen.size > 512 then return none
      match e with
      | .app f a => pending := pending ++ #[f, a]
      | .lam _ t b _ | .forallE _ t b _ => pending := pending ++ #[t, b]
      | .letE _ t v b _ => pending := pending ++ #[t, v, b]
      | .proj _ _ v | .mdata _ v => pending := pending.push v
      | _ => pure ()
  tryCatchRuntimeEx (do
    let mut thms ← getSimpTheorems
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail then
        let fact := decl.toExpr
        if ← isProp (← inferType fact) then
          thms ← thms.add (.fvar decl.fvarId) #[] fact
          let normalized ← StepEval.normalizeLookupFact fact
          if normalized != fact then
            thms ← thms.add (.other (← mkFreshUserName `frameFact)) #[] normalized
    let context ← Simp.mkContext {maxSteps := 2000, dsimp := true, decide := false}
      #[thms] (← getSimpCongrTheorems)
    let (reduced, _) ← StepEval.simpSteps target context #[← Simp.getSimprocs] none
    if reduced.expr.isConstOf ``True then
      if let some proof := reduced.proof? then return some (← mkOfEqTrue proof)
    return none) (fun _ => pure none)

/-- Case-split a goal on a recursor major premise (generalized first when it is not a
variable). `close` must prove every branch target; otherwise nothing is returned. -/
def casesOnRecursorMajor? (target : Expr) (recursor : Name) (args : Array Expr)
    (close : Expr → MetaM (Option Expr)) : MetaM (Option Expr) := do
  let .recInfo info ← getConstInfo recursor | return none
  let majorIdx := info.getMajorIdx
  let some major := args[majorIdx]? | return none
  if major.hasLooseBVars then return none
  let ty ← whnf (← inferType major)
  let .const typeName _ := ty.getAppFn | return none
  let .inductInfo indInfo ← getConstInfo typeName | return none
  if indInfo.isRec || indInfo.numIndices != 0 || indInfo.ctors.length > 16 then return none
  let saved ← saveState
  let proof? ← tryCatchRuntimeEx (do
    let goal ← mkFreshExprSyntheticOpaqueMVar target
    let (fvar, splitGoal) ← if major.isFVar then
        pure (major.fvarId!, goal.mvarId!)
      else do
        let mut targets : Array GeneralizeArg := #[{ expr := major }]
        for extra in args.extract (majorIdx+1) args.size do
          if (← inferType extra).find? (· == major) |>.isSome then
            targets := targets.push { expr := extra }
        let (fvars, g) ← goal.mvarId!.generalize targets
        pure (fvars[0]!, g)
    for branch in ← splitGoal.cases fvar do
      branch.mvarId.withContext do
        let branchTarget ← instantiateMVars (← branch.mvarId.getType)
        let some proof ← close branchTarget | throwError "recursor branch remains open"
        unless ← isDefEq (← inferType proof) branchTarget do
          throwError "recursor branch has wrong target"
        branch.mvarId.assign proof
    let proof ← instantiateMVars goal
    if proof.hasMVar then return none
    return some proof) (fun _ => pure none)
  if proof?.isNone then saved.restore
  return proof?

/-- One cheap reduction step: beta/iota/projection (whnfCore), then unfolding a structure
projection function applied to its structure. -/
def valueStep? (e : Expr) : MetaM (Option Expr) := do
  let core ← whnfCore e
  if core != e then return some core
  if let .const name _ := e.getAppFn then
    if let some info ← getProjectionFnInfo? name then
      if e.getAppNumArgs == info.numParams + 1 then
        if let some unfolded ← unfoldDefinition? e then
          let unfolded := unfolded.headBeta
          if unfolded != e then return some unfolded
  return none

/-- Peel a chain of projections (`Expr.proj` or projection-function applications). -/
partial def projectionSpine (e : Expr) : MetaM (Array (Expr → MetaM Expr) × Expr) := do
  match e with
  | .proj typeName index inner =>
    let (rest, core) ← projectionSpine inner
    return (rest.push (fun x => pure (.proj typeName index x)), core)
  | _ =>
    if let .const name _ := e.getAppFn then
      if let some info ← getProjectionFnInfo? name then
        if e.getAppNumArgs == info.numParams + 1 then
          let params := e.getAppArgs.extract 0 info.numParams
          let (rest, core) ← projectionSpine e.appArg!
          return (rest.push (fun x => pure (mkAppN e.getAppFn (params.push x))), core)
    return (#[], e)

partial def valueFrameEq? (lhs rhs : Expr) (depth : Nat := 0) : MetaM (Option Expr) := do
  if depth > 256 then return none
  let lhs := lhs.consumeMData.headBeta
  if ← withReducible (isDefEq lhs rhs) then
    return some (← mkExpectedTypeHint (← mkEqRefl rhs) (← mkEq lhs rhs))
  let hint (proof : Expr) : MetaM Expr := do mkExpectedTypeHint proof (← mkEq lhs rhs)
  let rhsCore ← whnfCore rhs
  if let some lctor ← isConstructorApp? lhs then
    if let some rctor ← isConstructorApp? rhsCore then
      if lctor.name == rctor.name && lhs.getAppNumArgs == rhsCore.getAppNumArgs
          && lhs.getAppNumArgs == lctor.numParams + lctor.numFields then
        let la := lhs.getAppArgs
        let ra := rhsCore.getAppArgs
        let mut ok := true
        for i in [0:lctor.numParams] do
          unless ← withReducible (isDefEq la[i]! ra[i]!) do ok := false
        if ok then
          let mut proof ← mkEqRefl (mkAppN lhs.getAppFn (la.extract 0 lctor.numParams))
          let mut failed := false
          for i in [lctor.numParams:la.size] do
            let argProof ← if la[i]! == ra[i]! then mkEqRefl la[i]! else
              match ← valueFrameEq? la[i]! ra[i]! (depth+1) with
              | some q => pure q
              | none => do failed := true; mkEqRefl la[i]!
            if failed then break
            proof ← mkCongr proof argProof
          unless failed do return some (← hint proof)
  if let some next ← valueStep? lhs then
    let some proof ← valueFrameEq? next rhs (depth+1) | return none
    return some (← hint proof)
  let (spine, core) ← projectionSpine lhs
  let coreType ← inferType core
  let project ← withLocalDeclD `frameCore coreType fun x => do
    let mut out := x
    for build in spine do out ← build out
    mkLambdaFVars #[x] out
  if spine.size > 0 then
    if let some next ← valueStep? core then
      let some proof ← valueFrameEq? (mkApp project next).headBeta rhs (depth+1) | return none
      return some (← hint proof)
    if let some next ← valueStep? (← spine[0]! core) then
      let mut rebuilt := next
      for build in spine.extract 1 spine.size do rebuilt ← build rebuilt
      if rebuilt != lhs then
        let some proof ← valueFrameEq? rebuilt rhs (depth+1) | return none
        return some (← hint proof)
  let f := core.getAppFn
  let args := core.getAppArgs
  if (f.isConstOf ``ite || f.isConstOf ``dite) && args.size == 5 then
    let mut proofs := #[]
    for branch in [0:2] do
      let condition := if branch == 0 then args[1]! else mkNot args[1]!
      let proof? ← withLocalDeclD `valueBranch condition fun h => do
        let value := if f.isConstOf ``dite then mkApp args[3+branch]! h else args[3+branch]!
        let some proof ← valueFrameEq? (mkApp project value).headBeta rhs (depth+1) | return none
        return some (← mkLambdaFVars #[h] proof)
      let some proof := proof? | return none
      proofs := proofs.push proof
    let lemma := if f.isConstOf ``dite then ``StepRuntime.value_dite_eq else ``StepRuntime.value_ite_eq
    let proof := mkAppN (mkConst lemma) #[coreType, ← inferType rhs, project, rhs, args[1]!, args[2]!,
      args[3]!, args[4]!, proofs[0]!, proofs[1]!]
    return some (← hint proof)
  if let .const recName _ := f then
    if (← getConstInfo recName) matches .recInfo _ then
      let target ← mkEq lhs rhs
      return ← casesOnRecursorMajor? target recName args fun branchTarget => do
        let some (_, left, right) := branchTarget.eq? | return none
        valueFrameEq? left right (depth+1)
  if spine.size > 0 then
   if let some unfolded ← unfoldDefinition? core then
    let unfolded := unfolded.headBeta
    if unfolded != core then
      let some proof ← valueFrameEq? (mkApp project unfolded).headBeta rhs (depth+1) | return none
      return some (← hint proof)
  return none

partial def projectedFrameEq? (project initial current : Expr)
    (depth : Nat := 0) : MetaM (Option Expr) := do
  if depth > 64 then return none
  let expected := (mkApp project initial).headBeta
  let actual := (mkApp project current).headBeta
  if ← isDefEq actual expected then
    return some (← mkExpectedTypeHint (← mkEqRefl expected) (← mkEq actual expected))
  let current := current.consumeMData.headBeta
  let f := current.getAppFn
  let args := current.getAppArgs
  if (f.isConstOf ``ite || f.isConstOf ``dite) && args.size == 5 then
    let mut proofs := #[]
    for branch in [0:2] do
      let condition := if branch == 0 then args[1]! else mkNot args[1]!
      let proof? ← withLocalDeclD `frameBranch condition fun h => do
        let value := if f.isConstOf ``dite then mkApp args[3+branch]! h else args[3+branch]!
        let some proof ← projectedFrameEq? project initial value (depth+1) | return none
        return some (← mkLambdaFVars #[h] proof)
      let some proof := proof? | return none
      proofs := proofs.push proof
    let lemma := if f.isConstOf ``dite then ``StepRuntime.projected_dite_eq
      else ``StepRuntime.projected_ite_eq
    return some (← mkAppM lemma #[project, initial, args[1]!, args[3]!, args[4]!, proofs[0]!, proofs[1]!])
  if let some proof ← valueFrameEq? actual expected (depth+1) then
    return some (← mkExpectedTypeHint proof (← mkEq actual expected))
  let projected ← withTransparency .all <| whnf actual
  if let some proof ← frameLocalEq? projected expected then
    return some (← mkExpectedTypeHint proof (← mkEq actual expected))
  if projected != actual then
    let identity ← withLocalDeclD `frameValue (← inferType expected) fun value =>
      mkLambdaFVars #[value] value
    let some proof ← projectedFrameEq? identity expected projected (depth+1) | return none
    return some (← mkExpectedTypeHint proof (← mkEq actual expected))
  let path : System.FilePath := "logs/driver-projection-unknown.txt"
  let size : UInt64 ← if ← path.pathExists then do pure (← path.metadata).byteSize else pure 0
  if size < 12000 then
    let text ← withOptions (fun options => options.set `pp.maxDepth (4 : Nat) |>.set `pp.maxSteps (200 : Nat)) do
      pure s!"depth={depth} project={← ppExpr project} expected={← ppExpr expected} actual={← ppExpr actual}\n"
    IO.FS.withFile path .append fun out => out.putStr text
  return none

/-- Infer a frame only from checked native state projections and generic loop
induction. Failure leaves the ordinary unframed path; no invariant is assumed. -/
partial def nativeSuccessFrame? (project initial result : Expr)
    (depth : Nat := 0) : MetaM (Option Expr) := do
  if depth > 256 then return none
  let result := result.consumeMData.headBeta
  let f := result.getAppFn
  let args := result.getAppArgs
  if f.isConstOf ``EStateM.Result.error then return some (mkConst ``True.intro)
  if f.isConstOf ``EStateM.Result.ok then
    return ← projectedFrameEq? project initial args.back! (depth+1)
  if (f.isConstOf ``ite || f.isConstOf ``dite) && args.size == 5 then
    let mut proofs := #[]
    for branch in [0:2] do
      let condition := if branch == 0 then args[1]! else mkNot args[1]!
      let proof? ← withLocalDeclD `frameBranch condition fun h => do
        let value := if f.isConstOf ``dite then mkApp args[3+branch]! h else args[3+branch]!
        let some proof ← nativeSuccessFrame? project initial value (depth+1) | return none
        return some (← mkLambdaFVars #[h] proof)
      let some proof := proof? | return none
      proofs := proofs.push proof
    let lemma := if f.isConstOf ``dite then ``StepRuntime.successFrame_dite
      else ``StepRuntime.successFrame_ite
    return some (← mkAppM lemma #[project, initial, args[1]!, args[3]!, args[4]!, proofs[0]!, proofs[1]!])
  if f.isConstOf ``StepRuntime.nativeIntRangeLoop && args.size == 7 then
    let body := args[5]!
    let bodyFrame? ← forallTelescopeReducing (← inferType body) fun inputs _ => do
      unless inputs.size == 4 do return none
      let some proof ← nativeSuccessFrame? project inputs[3]! (mkAppN body inputs) (depth+1)
        | return none
      return some (← mkLambdaFVars inputs proof)
    if bodyFrame?.isNone then
      let fixedFrame? ← forallTelescopeReducing (← inferType body) fun inputs _ => do
        unless inputs.size == 4 do return none
        let some proof ← nativeSuccessFrame? project initial (mkAppN body inputs) (depth+1)
          | return none
        return some (← mkLambdaFVars inputs proof)
      let some fixedFrame := fixedFrame? | return none
      let some same ← projectedFrameEq? project initial args[6]! (depth+1) | return none
      return some (← mkAppM ``StepRuntime.nativeIntRangeLoop_frame_fixed
        #[project, args[3]!, args[4]!, body, initial, args[6]!, fixedFrame, same])
    let some bodyFrame := bodyFrame? | return none
    let some same ← projectedFrameEq? project initial args[6]! (depth+1) | return none
    let frame ← mkAppM ``StepRuntime.nativeIntRangeLoop_frame
      #[project, args[3]!, args[4]!, body, bodyFrame, args[6]!]
    return some (← mkAppM ``StepRuntime.successFrame_trans
      #[project, initial, args[6]!, result, same, frame])
  if f.isConstOf ``StepRuntime.nativeExceptIntRangeLoop && args.size == 8 then
    let body := args[6]!
    let bodyFrame? ← forallTelescopeReducing (← inferType body) fun inputs _ => do
      unless inputs.size == 4 do return none
      let some proof ← nativeSuccessFrame? project inputs[3]! (mkAppN body inputs) (depth+1)
        | return none
      return some (← mkLambdaFVars inputs proof)
    if bodyFrame?.isNone then
      let fixedFrame? ← forallTelescopeReducing (← inferType body) fun inputs _ => do
        unless inputs.size == 4 do return none
        let some proof ← nativeSuccessFrame? project initial (mkAppN body inputs) (depth+1)
          | return none
        return some (← mkLambdaFVars inputs proof)
      let some fixedFrame := fixedFrame? | return none
      let some same ← projectedFrameEq? project initial args[7]! (depth+1) | return none
      return some (← mkAppM ``StepRuntime.nativeExceptIntRangeLoop_frame_fixed
        #[project, args[4]!, args[5]!, body, initial, args[7]!, fixedFrame, same])
    let some bodyFrame := bodyFrame? | return none
    let some same ← projectedFrameEq? project initial args[7]! (depth+1) | return none
    let frame ← mkAppM ``StepRuntime.nativeExceptIntRangeLoop_frame
      #[project, args[4]!, args[5]!, body, bodyFrame, args[7]!]
    return some (← mkAppM ``StepRuntime.successFrame_trans
      #[project, initial, args[7]!, result, same, frame])
  if f.isConstOf ``StepRuntime.resume && args.size == 6 then
    let some frame ← nativeSuccessFrame? project initial args[5]! (depth+1) | return none
    let continuationFrame? ← forallTelescopeReducing (← inferType args[4]!) fun inputs _ => do
      unless inputs.size == 2 do return none
      let some proof ← nativeSuccessFrame? project inputs[1]!
          (mkAppN args[4]! inputs) (depth+1) | return none
      return some (← mkLambdaFVars inputs proof)
    if continuationFrame?.isNone then
      let fixedFrame? ← forallTelescopeReducing (← inferType args[4]!) fun inputs _ => do
        unless inputs.size == 2 do return none
        let some proof ← nativeSuccessFrame? project initial
            (mkAppN args[4]! inputs) (depth+1) | return none
        return some (← mkLambdaFVars inputs proof)
      let some fixedFrame := fixedFrame? | return none
      return some (← mkAppM ``StepRuntime.resume_successFrame_fixed
        #[project, initial, args[4]!, args[5]!, frame, fixedFrame])
    let some continuationFrame := continuationFrame? | return none
    return some (← mkAppM ``StepRuntime.resume_successFrame
      #[project, initial, args[4]!, args[5]!, frame, continuationFrame])
  if f.isConstOf ``StepRuntime.resumeExcept && args.size == 7 then
    let some frame ← nativeSuccessFrame? project initial args[6]! (depth+1) | return none
    let continuationFrame? ← forallTelescopeReducing (← inferType args[5]!) fun inputs _ => do
      unless inputs.size == 2 do return none
      let some proof ← nativeSuccessFrame? project inputs[1]!
          (mkAppN args[5]! inputs) (depth+1) | return none
      return some (← mkLambdaFVars inputs proof)
    if continuationFrame?.isNone then
      let fixedFrame? ← forallTelescopeReducing (← inferType args[5]!) fun inputs _ => do
        unless inputs.size == 2 do return none
        let some proof ← nativeSuccessFrame? project initial
            (mkAppN args[5]! inputs) (depth+1) | return none
        return some (← mkLambdaFVars inputs proof)
      let some fixedFrame := fixedFrame? | return none
      return some (← mkAppM ``StepRuntime.resumeExcept_successFrame_fixed
        #[project, initial, args[5]!, args[6]!, frame, fixedFrame])
    let some continuationFrame := continuationFrame? | return none
    return some (← mkAppM ``StepRuntime.resumeExcept_successFrame
      #[project, initial, args[5]!, args[6]!, frame, continuationFrame])
  if let .letE _ _ value body _ := result then
    return ← nativeSuccessFrame? project initial (body.instantiate1 value) (depth+1)
  let core ← whnfCore result
  if core != result then return ← nativeSuccessFrame? project initial core (depth+1)
  if let some unfolded ← unfoldDefinition? result then
    let unfolded := unfolded.headBeta
    if unfolded != result then
      return ← nativeSuccessFrame? project initial unfolded (depth+1)
  let reduced ← whnf result
  if reduced != result then return ← nativeSuccessFrame? project initial reduced (depth+1)
  let discriminator? ← match f with
    | .const name _ => do
      match ← getConstInfo name with
      | .recInfo info => pure (args[info.getMajorIdx]?)
      | _ => pure none
    | _ => pure none
  if let some discriminator := discriminator? then
    if !discriminator.hasLooseBVars then
      let ty ← whnf (← inferType discriminator)
      if let .const typeName _ := ty.getAppFn then
        if let .inductInfo info ← getConstInfo typeName then
          if !info.isRec && info.numIndices == 0 && info.ctors.length <= 16 then
            let saved ← saveState
            let proof? ← tryCatchRuntimeEx (do
              let target ← mkAppM ``StepRuntime.SuccessFrame #[project, initial, result]
              let goal ← mkFreshExprSyntheticOpaqueMVar target
              let (major, splitGoal) ← if discriminator.isFVar then
                  pure (discriminator.fvarId!, goal.mvarId!)
                else do
                  let majorIdx := match ← getConstInfo f.constName! with
                    | .recInfo info => info.getMajorIdx
                    | _ => args.size
                  let mut targets : Array GeneralizeArg := #[{ expr := discriminator }]
                  for extra in args.extract (majorIdx+1) args.size do
                    if (← inferType extra).find? (· == discriminator) |>.isSome then
                      targets := targets.push { expr := extra }
                  let (fvars, g) ← goal.mvarId!.generalize targets
                  pure (fvars[0]!, g)
              let branches ← splitGoal.cases major
              for branch in branches do
                branch.mvarId.withContext do
                  let branchTarget ← instantiateMVars (← branch.mvarId.getType)
                  unless branchTarget.isAppOf ``StepRuntime.SuccessFrame do
                    throwError "constructor frame branch target is not a frame"
                  let targetArgs := branchTarget.getAppArgs
                  let some proof ← nativeSuccessFrame? targetArgs[targetArgs.size - 3]!
                    targetArgs[targetArgs.size - 2]! targetArgs[targetArgs.size - 1]! (depth+1)
                    | throwError "constructor frame branch remains open"
                  unless ← isDefEq (← inferType proof) (← branch.mvarId.getType) do
                    throwError "constructor frame branch has wrong target"
                  branch.mvarId.assign proof
              let proof ← instantiateMVars goal
              if proof.hasMVar then return none
              return some proof) (fun _ => pure none)
            if proof?.isSome then return proof?
            saved.restore
  let path : System.FilePath := "logs/driver-frame-unknown.txt"
  let size : UInt64 ← if ← path.pathExists then do pure (← path.metadata).byteSize else pure 0
  if size < 4096 then
    IO.FS.withFile path .append fun out =>
      out.putStrLn s!"depth={depth} resultHead={f.constName?} arity={args.size}"
  return none

/- Syntactic residual-call detection; the library traversal preserves DAG sharing. -/
/-- Beta plus structure-projection-of-constructor reduction, bottom-up. -/
def reduceRestored (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    let e := e.headBeta
    match e with
    | .proj _ index inner =>
      let inner := inner.headBeta
      if let .const name _ := inner.getAppFn then
        if let some ctor ← isConstructorApp? inner then
          if ctor.name == name then
            if let some field := inner.getAppArgs[ctor.numParams + index]? then
              return .done field
      return .done e
    | _ =>
      if let .const name _ := e.getAppFn then
        if let some info ← getProjectionFnInfo? name then
          if e.getAppNumArgs == info.numParams + 1 then
            let inner := e.appArg!.headBeta
            if let some ctor ← isConstructorApp? inner then
              if let some field := inner.getAppArgs[ctor.numParams + info.i]? then
                return .done (mkAppN field (e.getAppArgs.extract (info.numParams + 1) e.getAppNumArgs))
      return .done e)

/-- Register-file field indices (constructor argument positions) that `result` may write:
arguments of register-file constructor applications that are not the same field projection,
and targets of `RegisterRef.set`. Over-approximation only guides lens choice. -/
def writtenRegFields? (registerCtor : ConstructorVal) (result : Expr) : MetaM (Option (Array Nat)) := do
  let mut written : Std.HashSet Nat := {}
  let mut todo : Array Expr := #[result]
  let mut seen : Std.HashSet Expr := {}
  let regsTy := Lean.mkConst registerCtor.induct (registerCtor.levelParams.map mkLevelParam)
  let isSameField (i : Nat) (arg : Expr) : MetaM Bool := do
    match arg.consumeMData with
    | .proj typeName idx _ => pure (typeName == registerCtor.induct && idx + registerCtor.numParams == i)
    | e =>
      if let .const name _ := e.getAppFn then
        if let some info ← getProjectionFnInfo? name then
          return info.ctorName == registerCtor.name && info.i + registerCtor.numParams == i
      pure false
  while !todo.isEmpty do
    let e := todo.back!
    todo := todo.pop
    if seen.contains e then continue
    seen := seen.insert e
    if seen.size > 400000 then return none
    if e.isAppOf registerCtor.name && e.getAppNumArgs == registerCtor.numParams + registerCtor.numFields then
      let args := e.getAppArgs
      for i in [registerCtor.numParams:args.size] do
        unless ← isSameField i args[i]! do written := written.insert i
    if e.isAppOf ``Sail.ConcurrencyInterfaceV1.RegisterRef.set && e.getAppNumArgs ≥ 4 then
      let args := e.getAppArgs
      let probe? ← tryCatchRuntimeEx (withLocalDeclD `probeRegs regsTy fun fresh => do
        let applied ← whnf (mkAppN e.getAppFn ((args.extract 0 4).push fresh))
        unless applied.isAppOf registerCtor.name do return none
        let mut fields := #[]
        for i in [registerCtor.numParams:applied.getAppNumArgs] do
          let arg := applied.getAppArgs[i]!
          unless (← isSameField i arg) && arg.containsFVar fresh.fvarId! do fields := fields.push i
        return some fields) (fun _ => pure none)
      let some fields := probe? | return none
      for i in fields do written := written.insert i
    match e with
    | .app f a => todo := todo.push f |>.push a
    | .lam _ t b _ | .forallE _ t b _ => todo := todo.push t |>.push b
    | .letE _ t v b _ => todo := todo.push t |>.push v |>.push b
    | .mdata _ b | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  return some (written.toArray.qsort (· < ·))

/-- Lens over every register field except the (possibly) written ones; one frame search,
flat single-record restore. -/
def maskedRegsLens? (state result : Expr) : MetaM (Option (FrameLens × Expr)) := do
  let ty ← inferType state
  withLocalDeclD `maskedFrameState ty fun current => do
    let some expanded ← constructorEta? current | return none
    let .const ctor _ := expanded.getAppFn | return none
    let info ← getConstInfoCtor ctor
    let fields := expanded.getAppArgs
    let registers := fields[info.numParams]!
    let some registerExpanded ← constructorEta? registers | return none
    let .const registerCtor _ := registerExpanded.getAppFn | return none
    let registerInfo ← getConstInfoCtor registerCtor
    let registerFields := registerExpanded.getAppArgs
    let some written ← writtenRegFields? registerInfo result | return none
    if written.isEmpty || written.size * 2 > registerInfo.numFields then return none
    let atState := registerFields.map (·.replaceFVar current state)
    let maskedFields := (List.range registerFields.size).toArray.map fun i =>
      if written.contains i then atState[i]! else registerFields[i]!
    let project ← mkLambdaFVars #[current] (mkAppN registerExpanded.getAppFn maskedFields)
    let regsType ← inferType registers
    let restore ← withLocalDeclD `maskedRegisters regsType fun v => do
      let restoredFields := (List.range registerFields.size).toArray.map fun i =>
        if i < registerInfo.numParams then registerFields[i]!
        else if written.contains i then registerFields[i]!
        else Expr.proj registerInfo.induct (i - registerInfo.numParams) v
      let regs := mkAppN registerExpanded.getAppFn restoredFields
      mkLambdaFVars #[v, current] (mkAppN expanded.getAppFn (fields.set! info.numParams regs))
    let restored := mkApp2 restore (mkApp project current) current
    unless ← isDefEq restored current do return none
    let selfProof ← mkLambdaFVars #[current]
      (← mkExpectedTypeHint (← mkEqRefl current) (← mkEq restored current))
    let some frame ← nativeSuccessFrame? project state result | return none
    IO.FS.writeFile "logs/driver-masked-frame.txt" s!"PROVED_MASKED_REGISTER_FRAME written={written.toList}\n"
    return some (⟨project, restore, selfProof⟩, frame)

/-- Preserve the maximal set of independently proved record fields. Combining
frames preserves each field, while restoration leaves all other data intact. -/
def nativePreservedRegsLens? (state result : Expr) : MetaM (Option (FrameLens × Expr)) := do
  if let some lens ← nativeRegsLens? state then
    if let some frame ← nativeSuccessFrame? lens.project state result then
      return some (lens, frame)
  let ty ← inferType state
  unless ← isState ty do return none
  if let some masked ← maskedRegsLens? state result then return some masked
  withLocalDeclD `fieldFrameState ty fun current => do
    let some expanded ← constructorEta? current | return none
    let .const ctor _ := expanded.getAppFn | return none
    let info ← getConstInfoCtor ctor
    let fields := expanded.getAppArgs
    let registers := fields[info.numParams]!
    let some registerExpanded ← constructorEta? registers | return none
    let .const registerCtor _ := registerExpanded.getAppFn | return none
    let registerInfo ← getConstInfoCtor registerCtor
    let registerFields := registerExpanded.getAppArgs
    let mut combined : Option (FrameLens × Expr) := none
    for i in [registerInfo.numParams:registerFields.size] do
      let value := registerFields[i]!
      let project ← mkLambdaFVars #[current] value
      let some frame ← nativeSuccessFrame? project state result | continue
      let restore ← withLocalDeclD `preservedField (← inferType value) fun replacement => do
        let regs := mkAppN registerExpanded.getAppFn (registerFields.set! i replacement)
        mkLambdaFVars #[replacement, current]
          (mkAppN expanded.getAppFn (fields.set! info.numParams regs))
      let selfType ← mkEq (mkApp2 restore (mkApp project current) current) current
      unless ← isDefEq (mkApp2 restore (mkApp project current) current) current do continue
      let selfProof ← mkLambdaFVars #[current] (← mkExpectedTypeHint (← mkEqRefl current) selfType)
      let lens : FrameLens := ⟨project, restore, selfProof⟩
      match combined with
      | none => combined := some (lens, frame)
      | some (previous, previousFrame) =>
        let valuePair ← mkAppM ``Prod.mk #[mkApp previous.project current, mkApp project current]
        let pairType ← inferType valuePair
        let pairProject ← mkLambdaFVars #[current] valuePair
        let pairRestore ← withLocalDeclD `preservedFields pairType fun pair => do
          let first ← mkAppM ``Prod.fst #[pair]
          let second ← mkAppM ``Prod.snd #[pair]
          mkLambdaFVars #[pair, current]
            (mkApp2 previous.restore first (mkApp2 restore second current))
        let restored := mkApp2 pairRestore (mkApp pairProject current) current
        unless ← isDefEq restored current do continue
        let selfProof ← mkLambdaFVars #[current]
          (← mkExpectedTypeHint (← mkEqRefl current) (← mkEq restored current))
        let pairFrame ← mkAppM ``StepRuntime.successFrame_pair
          #[previous.project, project, state, result, previousFrame, frame]
        combined := some (⟨pairProject, pairRestore, selfProof⟩, pairFrame)
    if combined.isSome then
      IO.FS.writeFile "logs/driver-field-frame.txt" "PROVED_RECORD_FIELD_FRAME\n"
    return combined

def containsCalleeNative (e : Expr) (names : Array Name) : Bool :=
  !names.isEmpty && e.getUsedConstants.any names.contains

def containsOpaque (e : Expr) (names : Array Name) : Bool :=
  !names.isEmpty && e.getUsedConstants.any names.contains

mutual
partial def finiteMatcherControl (e discriminator : Expr) : EvalM (Option EvalResult) := do
  let rec select : Nat → Array Expr → EvalM (Option (Expr × Nat))
    | 0, _ => pure none
    | fuel+1, excluded => do
      let some (control,width) ← FiniteControl.choose discriminator 4 excluded | return none
      let normalized ← normalizeValue control
      if normalized.expr != control then select fuel (excluded.push control)
      else pure (some (control,width))
  let some (control,width) ← select ((collectFVars {} discriminator).fvarSet.toList.length+1) #[] | return none
  let (values,_,coverProof) ← FiniteControl.cover width
  let c ← read
  let initial ← get
  let callback := fun (term : Expr) (facts : Array Expr) (state : Stats) => do
    let mut thms := c.simp.simpTheorems[0]!
    for fact in facts do
      thms ← thms.add (.other (← mkFreshUserName `finiteLocal)) #[] fact
    let simp := c.simp.setSimpTheorems #[thms]
    let (result,nextState) ← ((evaluate term).run {c with simp}).run state
    pure (FiniteControl.Result.mk result.expr result.proof nextState)
  let result ← FiniteControl.branches callback e control values 0 (mkApp coverProof control) #[] initial
  set result.state
  return some ⟨result.expr,result.proof⟩

partial def evaluate (e : Expr) : EvalM EvalResult := do
  if let some r := (← get).cache[e]? then
    let context ← getLCtx
    let used := (collectFVars (collectFVars {} r.expr) r.proof).fvarSet
    if used.toList.all (fun id => (context.find? id).isSome) then
      modify fun st => {st with cacheHits := st.cacheHits + 1}
      return r
  let r ← evaluateCore e
  IO.FS.writeFile "logs/driver-cache.txt" "cache insert enter"
  unless r.expr.hasMVar || r.proof.hasMVar do
    modify fun st => {st with cache := st.cache.insert e r}
  IO.FS.writeFile "logs/driver-cache.txt" "cache insert returned"
  return r

partial def evaluateCore (e : Expr) : EvalM EvalResult := do
  IO.FS.writeFile "logs/driver-entry.txt" s!"raw head={e.getAppFn.constName?} args={e.getAppNumArgs} mvars={e.hasMVar}"
  let e := (← instantiateMVars e).consumeMData
  modify fun st => { st with steps := st.steps + 1 }
  let n := (← get).steps
  let maxSteps := ((← IO.getEnv "EVAL_MAX_STEPS").getD "100000").toNat!
  if n > maxSteps then throwError "standalone evaluator exceeded {maxSteps} head steps"
  IO.FS.withFile "logs/driver.trace.txt" .append fun h =>
    h.putStrLn s!"head {n}: {e.getAppFn.constName?} args={e.getAppNumArgs}"
  let args := e.getAppArgs
  let fn := e.getAppFn
  if let .const name _ := fn then
    if (← read).opaqueNames.contains name then return ← refl e
  if fn.isConstOf ``ite || fn.isConstOf ``dite then
    let msg ← withOptions (fun o => o.set `pp.maxSteps (2000 : Nat)) do
      pure s!"head={n} condition={← ppExpr args[1]!}\n"
    IO.FS.writeFile "logs/driver-condition-frontier.txt" msg
  if let .mdata _ inner := fn then
    let next := mkAppN inner args
    let nr ← evaluate next
    return ⟨nr.expr, ← mkExpectedTypeHint nr.proof (← mkEq e nr.expr)⟩
  if let some r ← prepareInputs e then
    let nr ← evaluate r.expr
    return ← compose e nr.expr (← chain r.proof nr.proof)
  let c ← read
  if fn.isConstOf ``IntRange.forIn' && args.size == 7 then
    let resultType ← whnf (← inferType e)
    if resultType.isAppOfArity ``EStateM.Result 3 then
      let body := args[5]!
      let isExcept ← forallTelescopeReducing (← inferType body) fun _ output => do
        let output ← whnf output
        return output.isAppOfArity ``EStateM.Result 3 &&
          output.getAppArgs[2]!.isAppOfArity ``Except 2
      if let some lens ← nativeRegsLens? args[6]! then
        let initialStats ← get
        let candidate? ← tryCatchRuntimeEx (do
          let (bodyCandidate?, nextStats) ←
              forallTelescopeReducing (← inferType body) fun inputs _ => do
            unless inputs.size == 4 do return (none, initialStats)
            let restored ← reduceRestored (mkApp2 lens.restore (mkApp lens.project args[6]!) inputs[3]!)
            let invocation := mkAppN body (inputs.set! 3 restored)
            let mut thms := c.simp.simpTheorems[0]!
            for input in inputs do
              if ← isProp (← inferType input) then
                thms ← thms.add (.fvar input.fvarId!) #[] input
            let simp := c.simp.setSimpTheorems #[thms]
            let (result, next) ← ((evaluate invocation).run {c with simp}).run initialStats
            let some frame ← nativeSuccessFrame? lens.project args[6]! result.expr
              | return (none, initialStats)
            let (value, proof) := ShareCommon.shareCommon (result.expr, result.proof)
            pure (some (← mkLambdaFVars inputs value,
              ← mkLambdaFVars inputs proof, ← mkLambdaFVars inputs frame), next)
          let some (nativeBody, bodyProof, bodyFrame) := bodyCandidate? | return none
          let lemma := if isExcept then ``StepRuntime.exceptIntRangeLoop_transport_frame
            else ``StepRuntime.intRangeLoop_transport_frame
          let proof ← mkAppM lemma #[lens.project, lens.restore, lens.selfProof,
            args[3]!, args[4]!, body, nativeBody, args[6]!, bodyProof, bodyFrame]
          let (native, proof) ← align e proof
          return some (native, proof, nextStats)) (fun _ => pure none)
        if let some (native, proof, nextStats) := candidate? then
          set nextStats
          IO.FS.writeFile "logs/driver-invariant-loop.txt" "BODY_FRAME_TRANSPORT_PROVED\n"
          return ← sharedCompose e native proof
      let stats ← get
      let ((nativeBody, bodyProof), nextStats) ←
          forallTelescopeReducing (← inferType body) fun inputs _ => do
        unless inputs.size == 4 do
          throwError "range body binders={inputs.size}: {← ppExpr (← inferType body)}"
        let mut thms := c.simp.simpTheorems[0]!
        for input in inputs do
          if ← isProp (← inferType input) then
            thms ← thms.add (.fvar input.fvarId!) #[] input
        let simp := c.simp.setSimpTheorems #[thms]
        let (result, state) ← ((evaluate (mkAppN body inputs)).run {c with simp}).run stats
        let (value, proof) := ShareCommon.shareCommon (result.expr, result.proof)
        pure ((← mkLambdaFVars inputs value, ← mkLambdaFVars inputs proof), state)
      set nextStats
      let nativeLemma := if isExcept then ``StepRuntime.nativeExceptIntRangeLoop
        else ``StepRuntime.nativeIntRangeLoop
      let congrLemma := if isExcept then ``StepRuntime.exceptIntRangeLoop_congr
        else ``StepRuntime.intRangeLoop_congr
      let native ← mkAppM nativeLemma #[args[3]!, args[4]!, nativeBody, args[6]!]
      let proof ← mkAppM congrLemma
        #[args[3]!, args[4]!, body, nativeBody, args[6]!, bodyProof]
      let (native, proof) ← align e proof
      return ← sharedCompose e native proof
  let discharge : Simp.Discharge := fun p => do
    let preview ← withOptions (fun o => o.set `pp.maxDepth (8 : Nat) |>.set `pp.maxSteps (2000 : Nat)) do
      pure (toString (← ppExpr p))
    IO.FS.writeFile "logs/driver-summary-premise.txt" preview
    let shaped? ← tryCatchRuntimeEx (do
      let mut cur := p
      let mut pf ← mkEqRefl p
      for _ in [0:32] do
        let (r, _) ← StepEval.simpSteps cur c.simp c.procs none
        let edge ← match r.proof? with
          | some proof => pure proof
          | none => mkExpectedTypeHint (← mkEqRefl cur) (← mkEq cur r.expr)
        pf ← chain pf edge
        if r.expr.isConstOf ``True then return some (← mkOfEqTrue pf)
        if r.expr == cur then break
        cur := r.expr
      pure none) (fun _ => pure none)
    if let some pf := shaped? then return some pf
    if let some (true, pf) ← arithmeticDecision p then return some pf
    return none
  let (callee?, _) ← Simp.SimpM.run c.simp {} (Simp.mkMethods c.procs discharge false) do
    Simp.rewrite? e c.summaries.post c.summaries.erased "step_summary" false
  if let some r := callee? then
    let pf ← match r.proof? with
      | some pf => pure pf
      | none => mkExpectedTypeHint (← mkEqRefl e) (← mkEq e r.expr)
    if c.compositionalNative then
      if let .const name _ := r.expr.getAppFn then
        let declared ← getConstInfo name
        let definition := match declared with
          | .defnInfo _ | .opaqueInfo _ => true
          | _ => false
        let resultType ← whnf (← inferType r.expr)
        let flat ← if r.expr.isAppOf ``EStateM.Result.ok then pure true else do
          match ← StepEval.deltaBeforeStateCore r.expr with
          | some unfolded => pure ((← whnfCore unfolded.expr.headBeta).isAppOf ``EStateM.Result.ok)
          | none => pure false
        if definition && !flat && resultType.isAppOfArity ``EStateM.Result 3 then
          compositionalCalleesRef.modify fun names => if names.contains name then names else names.push name
          IO.FS.withFile "logs/driver-compositional-callees.txt" .append fun out =>
            out.putStrLn s!"source={fn.constName?} native={name} summary_proof_constants={pf.getUsedConstants.toList}"
          return ← sharedCompose e r.expr pf
    if isNativeResultTree r.expr then return ⟨r.expr, pf⟩
    if let some unfolded ← StepEval.deltaBeforeStateCore r.expr then
      let native := unfolded.expr.headBeta
      if isNativeResultTree native then
        let edge ← mkExpectedTypeHint unfolded.proof?.get! (← mkEq r.expr native)
        return ⟨native, ← chain pf edge⟩
    let nr ← evaluate r.expr
    return ← compose e nr.expr (← chain pf nr.proof)
  if let some r ← conditional e then
    let nr ← evaluate r.expr
    return ← compose e nr.expr (← chain r.proof nr.proof)
  if (fn.isConstOf ``ite || fn.isConstOf ``dite) && (args.size == 6 || args.size == 5) then
    let c ← read
    let p := args[1]!
    let mut branchNatives := #[]
    let mut branchProofs := #[]
    for i in [0:2] do
      IO.FS.writeFile "logs/driver-phase.txt" s!"split branch {i}: entering"
      let ht ← if i == 0 then pure p else pure (mkNot p)
      let st ← get
      let ((v, pf), st') ← withLocalDeclD `branchCondition ht fun h => do
        let mut thms := c.simp.simpTheorems[0]!
        IO.FS.writeFile "logs/driver-phase.txt" s!"split branch {i}: adding hypothesis"
        thms ← thms.add (.fvar h.fvarId!) #[] h
        IO.FS.writeFile "logs/driver-phase.txt" s!"split branch {i}: hypothesis added"
        let simp := c.simp.setSimpTheorems #[thms]
        let branch := if fn.isConstOf ``dite then mkApp args[3 + i]! h else args[3 + i]!
        let input := if args.size == 6 then mkApp branch args[5]! else branch
        IO.FS.writeFile "logs/driver-phase.txt" s!"split branch {i}: calling evaluator"
        let (r, st') ← ((evaluate input).run {c with simp}).run st
        IO.FS.writeFile "logs/driver-phase.txt" s!"split branch {i}: evaluated"
        let (value, proof) := ShareCommon.shareCommon (r.expr, r.proof)
        IO.FS.writeFile "logs/driver-phase.txt" s!"split branch {i}: abstracting"
        let closed := (← mkLambdaFVars #[h] value, ← mkLambdaFVars #[h] proof)
        IO.FS.writeFile "logs/driver-phase.txt" s!"split branch {i}: sharing"
        return (ShareCommon.shareCommon closed, st')
      set st'
      branchNatives := branchNatives.push v
      branchProofs := branchProofs.push pf
    let lemma := if args.size == 6 then
        if fn.isConstOf ``dite then ``StepRuntime.split_dite else ``StepRuntime.split_ite
      else if fn.isConstOf ``dite then ``StepRuntime.split_value_dite else ``StepRuntime.split_value_ite
    let inputs ← if args.size == 6 then do
        let .forallE _ inputTy outputTy _ ← whnf args[0]! | throwError "conditional branch is not a function"
        pure #[inputTy, outputTy.instantiate1 args[5]!, p, args[2]!, args[3]!, args[4]!, args[5]!]
      else pure #[args[0]!, p, args[2]!, args[3]!, args[4]!]
    let pf := mkAppN (mkConst lemma) (inputs ++ #[branchNatives[0]!, branchNatives[1]!,
      branchProofs[0]!, branchProofs[1]!])
    IO.FS.writeFile "logs/driver-phase.txt" "split: aligning proof"
    let (out, pf) ← align e pf
    IO.FS.writeFile "logs/driver-phase.txt" "split: certifying"
    if branchNatives[0]!.isLambda && branchNatives[1]!.isLambda then
      let left := branchNatives[0]!.bindingBody!
      let right := branchNatives[1]!.bindingBody!
      if !left.hasLooseBVars && !right.hasLooseBVars && left == right then
        let mergeProof := mkAppN (mkConst ``StepRuntime.merge_dite)
          #[← inferType left, p, args[2]!, left]
        return ← sharedCompose e left (← chain pf mergeProof)
      let la := left.getAppArgs
      let ra := right.getAppArgs
      if left.getAppFn.isConstOf ``EStateM.Result.ok &&
          right.getAppFn.isConstOf ``EStateM.Result.ok &&
          la.size == 5 && ra.size == 5 then
        let .lam ln lt _ li := branchNatives[0]! | unreachable!
        let .lam rn rt _ ri := branchNatives[1]! | unreachable!
        let values := #[la[0]!,la[1]!,la[2]!,p,args[2]!,
            .lam ln lt la[3]! li, .lam rn rt ra[3]! ri]
        let factorProof := if !la[4]!.hasLooseBVars && la[4]! == ra[4]! then
            mkAppN (mkConst ``StepRuntime.factor_ok_dite) (values.push la[4]!)
          else mkAppN (mkConst ``StepRuntime.factor_ok_states_dite)
            (values ++ #[.lam ln lt la[4]! li, .lam rn rt ra[4]! ri])
        IO.FS.writeFile "logs/driver-phase.txt" "split: factoring"
        -- Construct the known RHS without instantiating the factoring lemma's
        -- dependent type over both complete branch bodies.
        let value := mkAppN (mkConst ``dite [← getLevel la[2]!])
          #[la[2]!, p, args[2]!, values[5]!, values[6]!]
        let state ← if !la[4]!.hasLooseBVars && la[4]! == ra[4]! then pure la[4]! else
          pure (mkAppN (mkConst ``dite [← getLevel la[1]!])
            #[la[1]!, p, args[2]!, .lam ln lt la[4]! li, .lam rn rt ra[4]! ri])
        let factored := mkAppN left.getAppFn #[la[0]!, la[1]!, la[2]!, value, state]
        let resultTy := mkAppN (mkConst ``EStateM.Result left.getAppFn.constLevels!)
          #[la[0]!, la[1]!, la[2]!]
        let combined := mkAppN (mkConst ``Eq.trans [← getLevel resultTy])
          #[resultTy, e, out, factored, pf, factorProof]
        IO.FS.writeFile "logs/driver-phase.txt" "split: factored"
        return ← sharedCompose e factored combined
    return ← sharedCompose e out pf
  if fn.isConstOf ``ite || fn.isConstOf ``dite || fn.isConstOf ``Bool.casesOn then
    IO.FS.writeFile s!"logs/driver-conditional-{n}.txt"
      (← withOptions (fun o => o.setBool `pp.explicit true) <| pure (toString (← ppExpr e)))
    if args.size > 2 then
      let mut msg := ""
      for a in args.extract 0 (min 3 args.size) do
        msg := msg ++ s!"\nARG {← ppExpr a} FV={a.hasFVar} MV={a.hasMVar}"
      unless args[2]!.hasFVar || args[2]!.hasMVar do
        msg := msg ++ s!"\nWHNF {← ppExpr (← StepEval.closedWhnf args[2]!)}"
      IO.FS.withFile s!"logs/driver-conditional-{n}.txt" .append fun h => h.putStrLn msg
  if fn.isConstOf ``EStateM.Result.ok || fn.isConstOf ``EStateM.Result.error then
    let a := args[args.size - 2]!
    let s := args.back!
    let av ← normalizeValue a
    let sv ← normalizeState s
    let lemma := if fn.isConstOf ``EStateM.Result.ok then ``StepRuntime.ok_congr else ``StepRuntime.error_congr
    let pf := mkAppN (mkConst lemma)
      #[args[0]!, args[1]!, args[2]!, a, av.expr, s, sv.expr, av.proof, sv.proof]
    let (out, pf) ← align e pf
    return ← compose e out pf
  if fn.isConstOf ``ExceptT.bind && args.size == 8 then
    let resultType ← whnf (← inferType e)
    if resultType.isAppOfArity ``EStateM.Result 3 then
      let x := args[5]!
      let k := args[6]!
      let state := args[7]!
      let stateType ← inferType state
      let xr ← evaluate (mkApp x state)
      let symbolicLoop := !xr.expr.getAppFn.isConstOf ``EStateM.Result.ok &&
        !xr.expr.getAppFn.isConstOf ``EStateM.Result.error &&
        (xr.expr.getUsedConstants.contains ``StepRuntime.nativeIntRangeLoop ||
          xr.expr.getUsedConstants.contains ``StepRuntime.nativeExceptIntRangeLoop ||
          containsCalleeNative xr.expr (← compositionalCalleesRef.get))
      if symbolicLoop then
        if let some (lens, frame) ← nativePreservedRegsLens? state xr.expr then
          let stats ← get
          let ((nativeK, continuationProof), stats') ← withLocalDeclD `exceptValue args[3]! fun value =>
            withLocalDeclD `exceptState stateType fun current => do
              let restored ← reduceRestored (mkApp2 lens.restore (mkApp lens.project state) current)
              let (result, next) ← ((evaluate (mkApp2 k value restored)).run c).run stats
              let (valueExpr, proof) := ShareCommon.shareCommon (result.expr, result.proof)
              pure ((← mkLambdaFVars #[value,current] valueExpr,
                ← mkLambdaFVars #[value,current] proof), next)
          set stats'
          let proof ← mkAppM ``StepRuntime.exceptBind_native_frame
            #[lens.project, lens.restore, lens.selfProof, x, k, nativeK,
              state, xr.expr, xr.proof, frame, continuationProof]
          let (native, proof) ← align e proof
          return ← sharedCompose e native proof
        let stats ← get
        let ((nativeK, continuationProof), stats') ← withLocalDeclD `exceptValue args[3]! fun value =>
          withLocalDeclD `exceptState stateType fun current => do
            let (result, next) ← ((evaluate (mkApp2 k value current)).run c).run stats
            let (valueExpr, proof) := ShareCommon.shareCommon (result.expr, result.proof)
            pure ((← mkLambdaFVars #[value,current] valueExpr,
              ← mkLambdaFVars #[value,current] proof), next)
        set stats'
        let proof ← mkAppM ``StepRuntime.exceptBind_native_cont
          #[x, k, nativeK, state, xr.expr, xr.proof, continuationProof]
        let (native, proof) ← align e proof
        return ← sharedCompose e native proof
  if fn.isConstOf ``EStateM.bind && args.size == 7 then
    let x := args[4]!
    let k := args[5]!
    let s := args[6]!
    let xr ← evaluate (mkApp x s)
    let xa := xr.expr.getAppArgs
    let xf := xr.expr.getAppFn
    if xf.isConstOf ``EStateM.Result.error then
      let pf := mkAppN (mkConst ``StepRuntime.bind_error)
        (args.extract 0 4 ++ #[x,k,s,xa[xa.size-2]!,xa.back!,xr.proof])
      let (out, pf) ← align e pf
      return ← compose e out pf
    let nativeLoop := !xf.isConstOf ``EStateM.Result.ok &&
      (xr.expr.getUsedConstants.contains ``StepRuntime.nativeIntRangeLoop ||
        xr.expr.getUsedConstants.contains ``StepRuntime.nativeExceptIntRangeLoop)
    let nativeComposed := !xf.isConstOf ``EStateM.Result.ok &&
      containsCalleeNative xr.expr (← compositionalCalleesRef.get)
    let frameableControl := !xf.isConstOf ``EStateM.Result.ok &&
      (nativeLoop || isNativeResultTree xr.expr || xf.isConstOf ``StepRuntime.resume)
    if nativeLoop || nativeComposed then
      if let some (lens, frame) ← nativePreservedRegsLens? s xr.expr then
        let stats ← get
        let ((nativeK, continuationProof), stats') ← withLocalDeclD `loopValue args[2]! fun a =>
          withLocalDeclD `loopState args[1]! fun current => do
            let restored ← reduceRestored (mkApp2 lens.restore (mkApp lens.project s) current)
            let (result, next) ← ((evaluate (mkApp2 k a restored)).run c).run stats
            let (value, proof) := ShareCommon.shareCommon (result.expr, result.proof)
            pure ((← mkLambdaFVars #[a,current] value,
              ← mkLambdaFVars #[a,current] proof), next)
        set stats'
        let native := mkAppN (mkConst ``StepRuntime.resume)
          (args.extract 0 4 ++ #[nativeK, xr.expr])
        let proof ← mkAppM ``StepRuntime.bind_native_frame
          #[lens.project, lens.restore, lens.selfProof, x, k, nativeK,
            s, xr.expr, xr.proof, frame, continuationProof]
        IO.FS.writeFile "logs/driver-loop-frame.txt" "REGISTER_FRAME_PROVED\n"
        return ← sharedCompose e native proof
    if nativeLoop || nativeComposed || (!c.opaqueNames.isEmpty && containsOpaque xr.expr c.opaqueNames) then
      IO.FS.withFile "logs/driver-frame-fallback.txt" .append fun out =>
        out.putStrLn s!"head={n} sourceAction={x.getAppFn.constName?} nativeHead={xf.constName?} nativeArity={xa.size} continuationHead={k.getAppFn.constName?}"
      let stats ← get
      let ((nativeK, continuationProof), stats') ← withLocalDeclD `opaqueValue args[2]! fun a =>
        withLocalDeclD `opaqueState args[1]! fun t => do
          let (r, stats') ← ((evaluate (mkApp2 k a t)).run c).run stats
          let (value, proof) := ShareCommon.shareCommon (r.expr, r.proof)
          pure ((← mkLambdaFVars #[a,t] value, ← mkLambdaFVars #[a,t] proof), stats')
      set stats'
      let native := mkAppN (mkConst ``StepRuntime.resume)
        (args.extract 0 4 ++ #[nativeK,xr.expr])
      let pf := mkAppN (mkConst ``StepRuntime.bind_native_cont)
        (args.extract 0 4 ++ #[x,k,nativeK,s,xr.expr,xr.proof,continuationProof])
      return ← sharedCompose e native pf
    unless xf.isConstOf ``EStateM.Result.ok do
      let edge := mkAppN (mkConst ``StepRuntime.bind_resume)
        (args.extract 0 4 ++ #[x,k,s,xr.expr,xr.proof])
      let (next, edge) ← align e edge
      let nr ← evaluate next
      return ← compose e nr.expr (← chain edge nr.proof)
    let originalState := xa.back!
    let stateHead := originalState.consumeMData.headBeta.getAppFn
    let stateResult ← if stateHead.isConstOf ``ite || stateHead.isConstOf ``dite then
      IO.FS.withFile "logs/driver-state-projection.txt" .append fun h =>
        h.putStrLn s!"factored state projection head={n}"
      normalizeRegisters originalState
      else refl originalState
    let next := mkApp2 k xa[xa.size-2]! stateResult.expr
    let edge := mkAppN (mkConst ``StepRuntime.bind_ok)
      (args.extract 0 4 ++ #[x,k,s,xa[xa.size-2]!,originalState,xr.proof])
    let (_, edge) ← align e edge
    let stateEdge ← mkCongrArg (mkApp k xa[xa.size-2]!) stateResult.proof
    let nr ← evaluate next
    return ← compose e nr.expr (← chain edge (← chain stateEdge nr.proof))
  if fn.isConstOf ``StepRuntime.resume && args.size == 6 then
    let k := args[4]!
    let r := args[5]!.consumeMData.headBeta
    let ra := r.getAppArgs
    let rf := r.getAppFn
    if rf.isConstOf ``StepRuntime.resume && ra.size == 6 then
      let proof ← mkAppM ``StepRuntime.resume_assoc #[k, ra[4]!, ra[5]!]
      let (next, proof) ← align e proof
      let result ← evaluate next
      return ← compose e result.expr (← chain proof result.proof)
    if rf.isConstOf ``ite || rf.isConstOf ``dite then
      let lemma := if rf.isConstOf ``dite then ``StepRuntime.resume_dite else ``StepRuntime.resume_ite
      let pf := mkAppN (mkConst lemma)
        (args.extract 0 4 ++ #[k, ra[1]!, ra[2]!, ra[3]!, ra[4]!])
      let (next, pf) ← align e pf
      let nr ← evaluate next
      return ← compose e nr.expr (← chain pf nr.proof)
    if rf.isConstOf ``EStateM.Result.ok || rf.isConstOf ``EStateM.Result.error then
      let next := if rf.isConstOf ``EStateM.Result.ok then mkApp2 k ra[3]! ra[4]!
        else mkAppN (mkConst ``EStateM.Result.error rf.constLevels!) #[ra[0]!,ra[1]!,args[3]!,ra[3]!,ra[4]!]
      let edge ← StepEval.certify e { expr := next }
      let nr ← evaluate next
      return ← compose e nr.expr (← chain edge.proof?.get! nr.proof)
    if containsCalleeNative r (← compositionalCalleesRef.get) ||
        r.getUsedConstants.contains ``StepRuntime.nativeIntRangeLoop ||
        r.getUsedConstants.contains ``StepRuntime.nativeExceptIntRangeLoop then
      if (← compositionalCalleesRef.get).contains rf.constName && !ra.isEmpty then
        let initial := ra.back!
        if ← isState (← inferType initial) then
          if let some (lens, frame) ← nativePreservedRegsLens? initial r then
            let stats ← get
            let ((nativeK, continuationProof), nextStats) ← withLocalDeclD `nativeValue args[2]! fun value =>
              withLocalDeclD `nativeState args[1]! fun current => do
                let restored ← reduceRestored (mkApp2 lens.restore (mkApp lens.project initial) current)
                let (result, next) ← ((evaluate (mkApp2 k value restored)).run c).run stats
                let (valueExpr, proof) := ShareCommon.shareCommon (result.expr, result.proof)
                pure ((← mkLambdaFVars #[value,current] valueExpr,
                  ← mkLambdaFVars #[value,current] proof), next)
            set nextStats
            let proof ← mkAppM ``StepRuntime.resume_native_frame
              #[lens.project, lens.restore, lens.selfProof, k, nativeK, initial, r, frame, continuationProof]
            let (native, proof) ← align e proof
            return ← sharedCompose e native proof
      let stats ← get
      let ((nativeK, continuationProof), nextStats) ← withLocalDeclD `nativeValue args[2]! fun value =>
        withLocalDeclD `nativeState args[1]! fun current => do
          let (result, next) ← ((evaluate (mkApp2 k value current)).run c).run stats
          let (valueExpr, proof) := ShareCommon.shareCommon (result.expr, result.proof)
          pure ((← mkLambdaFVars #[value,current] valueExpr,
            ← mkLambdaFVars #[value,current] proof), next)
      set nextStats
      let proof ← mkAppM ``StepRuntime.resume_native_cont #[k, nativeK, r, continuationProof]
      let (native, proof) ← align e proof
      return ← sharedCompose e native proof
    throwError "resume input is not a result or conditional: head={rf.constName?} arity={ra.size}"
  if let .const recName _ := fn then
    if let .recInfo info ← getConstInfo recName then
      let majorIdx := info.getMajorIdx
      if args.size > majorIdx then
        let originalMajor := args[majorIdx]!
        -- Nonrecursive structure eta exposes only demanded projections and is
        -- definitionally equal, including dependent structure field types.
        let major := (← constructorEta? originalMajor).getD originalMajor
        -- Constructor iota does not demand field normalization. In particular,
        -- rewriting a dependent major's fields first changes its codomain.
        let constructorHead ← match major.consumeMData.headBeta.getAppFn with
          | .const name _ => do
            match ← getConstInfo name with
            | .ctorInfo _ => pure true
            | _ => pure false
          | _ => pure false
        let mr ← if constructorHead then refl major else normalizeValue major
        if !constructorHead && mr.expr.hasFVar then
          if let some result ← finiteRecursorControl e mr.expr then return result
        unless ← isDefEq major mr.expr do
          let majorFn := mkAppN fn (args.extract 0 majorIdx)
          let .forallE _ _ resultType _ ← whnf (← inferType majorFn)
            | throwError "recursor major function is not a function"
          if resultType.hasLooseBVar 0 then
            let edge ← rewriteDependentMajor e majorIdx mr
            let result ← evaluate edge.expr
            return ← compose e result.expr (← chain edge.proof result.proof)
        let prefixArgs := (args.extract 0 (majorIdx + 1)).set! majorIdx mr.expr
        let firstMinor := info.getFirstMinorIdx
        let rec abstractMinors (i : Nat) (as' xs vs : Array Expr) : MetaM (Expr × Expr) := do
          if i < firstMinor + info.numMinors then
            let a := as'[i]!
            withLocalDeclD `minor (← inferType a) fun v =>
              abstractMinors (i + 1) (as'.set! i v) (xs.push v) (vs.push a)
          else
            let generic := mkAppN fn as'
            let some out ← reduceRecMatcher? generic | do
              let msg ← withOptions (fun o => o.set `pp.maxSteps (2000 : Nat)) do
                pure s!"recursor={recName} major={← ppExpr major}\nnormalized={← ppExpr mr.expr}\nfvars={mr.expr.hasFVar}\n"
              IO.FS.writeFile "logs/driver-recursor.txt" msg
              throwError "recursor major remains symbolic; diagnostic logs/driver-recursor.txt"
            let r ← StepEval.certify generic {expr := out}
            let some pf := r.proof? | throwError "recursor unchanged"
            return (out.replaceFVars xs vs, pf.replaceFVars xs vs)
        let (out, pf) ← abstractMinors firstMinor prefixArgs #[] #[]
        let originalPrefix := mkAppN fn (args.extract 0 (majorIdx + 1))
        let newPrefix := mkAppN fn prefixArgs
        -- Normalizing the major premise can use local equations, so its
        -- certificate must be lifted through the recursor instead of replaced
        -- by reflexivity (which is valid only for definitional reduction).
        let edge ← if ← isDefEq major mr.expr then
          -- Retain definitional reduction for dependent recursor motives.
          StepEval.certify originalPrefix {expr := newPrefix}
        else do
          let majorFn := mkAppN fn (args.extract 0 majorIdx)
          let majorProof ← mkCongrArg majorFn mr.proof
          StepEval.certify originalPrefix {expr := newPrefix, proof? := some majorProof}
        let mut pf ← match edge.proof? with | some ep => chain ep pf | none => pure pf
        let mut out := out
        for a in args.extract (majorIdx + 1) args.size do
          pf ← mkCongrFun pf a
          out := mkApp out a
        let nr ← evaluate out
        return ← compose e nr.expr (← chain pf nr.proof)
  -- Reduce an entire closed conditional before it is applied to a state.
  if let some r ← StepEval.closedIte e then
    let some pf := r.proof? | throwError "conditional missing proof"
    let nr ← evaluate r.expr
    return ← compose e nr.expr (← chain pf nr.proof)
  if let some r ← dependentConditional e then
    let nr ← evaluate r.expr
    return ← compose e nr.expr (← chain r.proof nr.proof)
  if let .const c _ := fn then
    if let some info ← getMatcherInfo? c then
      if info.numDiscrs == 1 then
        let di := info.numParams + 1
        let arity := di + 1 + info.numAlts
        if args.size >= arity then
          let d := args[di]!
          let dt ← whnf (← inferType d)
          let dr ← if dt.isAppOf ``EStateM.Result then evaluate d else normalizeValue d
          let matcher := mkAppN fn ((args.extract 0 arity).set! di dr.expr)
          let rf := dr.expr.getAppFn
          let ra := dr.expr.getAppArgs
          let conditionalDiscriminant := (rf.isConstOf ``ite || rf.isConstOf ``dite) && ra.size == 5
          let reducible ← if conditionalDiscriminant then pure false else
            pure (match ← reduceMatcher? matcher with | .reduced _ => true | _ => false)
          if !reducible && !conditionalDiscriminant then
            if let some result ← finiteMatcherControl e dr.expr then return result
          if !reducible &&
              !dr.expr.getAppFn.isConstOf ``ite && !dr.expr.getAppFn.isConstOf ``dite then
            if let .const enumName _ := dt then
              if let .inductInfo enumInfo ← getConstInfo enumName then
                let flat ← enumInfo.ctors.allM fun ctor => return (← getConstInfoCtor ctor).numFields == 0
                if enumInfo.numParams == 0 && flat then
                  let ef ← withLocalDeclD `enumValue dt fun v =>
                    mkLambdaFVars #[v] (e.replace fun t => if t == d then some v else none)
                  let mut values := #[]
                  let mut proofs := #[]
                  for ctor in enumInfo.ctors do
                    let r ← evaluate (mkApp ef (mkConst ctor)).headBeta
                    values := values.push r.expr
                    proofs := proofs.push r.proof
                  let same := values.all (· == values[0]!)
                  let resultTy ← inferType e
                  let nativeMotive ← withLocalDeclD `enumValue dt fun v => mkLambdaFVars #[v] resultTy
                  let casesName := enumName ++ `casesOn
                  let native ← if same then pure values[0]! else
                    mkAppOptM casesName (#[some nativeMotive, some d] ++ values.map some)
                  let proofMotive ← withLocalDeclD `enumValue dt fun v => do
                    let nv ← if same then pure native else
                      mkAppOptM casesName (#[some nativeMotive, some v] ++ values.map some)
                    mkLambdaFVars #[v] (← mkEq (mkApp ef v) nv)
                  let pf ← mkAppOptM casesName (#[some proofMotive, some d] ++ proofs.map some)
                  return ← compose e native pf
          let f ← withLocalDeclD `discriminant (← inferType d) fun v =>
            mkLambdaFVars #[v] (mkAppN fn ((args.extract 0 arity).set! di v))
          let (out, ipf) ← do
            if conditionalDiscriminant then
              let lemma := if rf.isConstOf ``dite then ``StepRuntime.apply_dite else ``StepRuntime.apply_ite
              let pf ← mkAppM lemma #[f, ra[1]!, ra[3]!, ra[4]!]
              align matcher pf
            else
              match ← reduceMatcher? matcher with
              | .reduced _ => StepEval.iotaCertificate matcher
              | _ => do
                IO.FS.writeFile "logs/driver-symbolic.txt"
                  s!"matcher={c} discrIndex={di} arity={arity}\ndiscrHead={d.getAppFn.constName?} discrArgs={d.getAppNumArgs}\ndiscrType={← ppExpr dt}\nnormalizedHead={dr.expr.getAppFn.constName?}\n"
                throwError "symbolic matcher remains in {c}; diagnostic logs/driver-symbolic.txt"
          let originalPrefix := mkAppN fn (args.extract 0 arity)
          let cp ← if ← isDefEq d dr.expr then
              mkExpectedTypeHint (← mkEqRefl originalPrefix) (← mkEq originalPrefix matcher)
            else mkCongrArg f dr.proof
          let mut pf ← chain cp ipf
          let mut out := out
          for a in args.extract arity args.size do
            pf ← mkCongrFun pf a
            out := mkApp out a
          let nr ← evaluate out
          return ← compose e nr.expr (← chain pf nr.proof)
  -- Class projections select a monad operation; only the function head is reduced.
  if let .proj .. := fn then
    if let some f ← withTransparency .all <| reduceProj? fn then
      let fp ← StepEval.certify fn { expr := f }
      let mut pf := fp.proof?.getD (← mkEqRefl fn)
      for a in args do pf ← mkCongrFun pf a
      let next := mkAppN f args
      let nr ← evaluate next
      return ← compose e nr.expr (← chain pf nr.proof)
  if fn.isLet then
    let .letE _ _ v b _ := fn | unreachable!
    let out := b.instantiate1 v
    let fp ← StepEval.certify fn { expr := out }
    let mut pf := fp.proof?.getD (← mkEqRefl fn)
    for a in args do pf ← mkCongrFun pf a
    let next := mkAppN out args
    let nr ← evaluate next
    return ← compose e nr.expr (← chain pf nr.proof)
  if fn.isLambda || e.isLet then
    let next := match e with
      | .letE _ _ v b _ => b.instantiate1 v
      | _ => e.headBeta
    if next == e then throwError "head beta made no progress"
    let pf ← mkExpectedTypeHint (← mkEqRefl e) (← mkEq e next)
    let edge ← certified e next pf
    let nr ← evaluate next
    return ← compose e nr.expr (← chain edge.proof nr.proof)
  let edge ← delta e
  if edge.expr == e then throwError "delta made no progress: {fn}"
  let nr ← evaluate edge.expr
  return ← compose e nr.expr (← chain edge.proof nr.proof)

/-- Exhaustively lift small finite controls from a symbolic recursion measure.
The bound is a search budget, never an instruction-domain restriction. Every
value is covered by a kernel-reduced closed finite enumeration certificate. -/
partial def finiteRecursorControl (e major : Expr) : EvalM (Option EvalResult) := do
  let rec select : Nat → Array Expr → EvalM (Option (Expr × Nat))
    | 0, _ => pure none
    | fuel+1, excluded => do
      let some (control,width) ← FiniteControl.choose major 3 excluded | return none
      let normalized ← normalizeValue control
      if normalized.expr != control then select fuel (excluded.push control)
      else pure (some (control,width))
  let some (control,width) ← select 256 #[] | return none
  let (values,_,coverProof) ← FiniteControl.cover width
  let c ← read
  let initial ← get
  let callback := fun (term : Expr) (facts : Array Expr) (state : Stats) => do
    let mut thms := c.simp.simpTheorems[0]!
    for fact in facts do
      thms ← thms.add (.other (← mkFreshUserName `recursorFiniteLocal)) #[] fact
    let simp := c.simp.setSimpTheorems #[thms]
    let (result,nextState) ← ((evaluate term).run {c with simp}).run state
    pure (FiniteControl.Result.mk result.expr result.proof nextState)
  IO.FS.writeFile "logs/driver-finite-control.txt"
    s!"width={width} alternatives={values.size} shared derived/FV control"
  let result ← FiniteControl.branches callback e control values 0
    (mkApp coverProof control) #[] initial
  set result.state
  return some ⟨result.expr,result.proof⟩

end

syntax (name := driveCmd) "drive_spec " ident ", " ident " : " term : command
@[command_elab driveCmd] def elabDrive : CommandElab := fun stx => do
  let `(drive_spec $ni:ident, $ti:ident : $t:term) := stx | throwUnsupportedSyntax
  let ns ← getCurrNamespace
  let nn := ns ++ ni.getId
  let tn := ns ++ ti.getId
  liftTermElabM do
    let e ← elabTerm t none
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    lambdaTelescope e fun xs body => do
      StepEval.resetLookupFactCaches
      let mut thms ← getSimpTheorems
      thms ← thms.addDeclToUnfold ``Sail.BitVec.length
      thms ← thms.addDeclToUnfold ``Sail.Vector.length
      let mut data := #[]
      let mut hyps := #[]
      for x in xs do
        if ← isProp (← inferType x) then
          thms ← thms.add (.fvar x.fvarId!) #[] x
          let normalized ← StepEval.normalizeLookupFact x
          if normalized != x then
            thms ← thms.add (.other (← mkFreshUserName `lookupFact)) #[] normalized
          hyps := hyps.push x
        else data := data.push x
      let ctx ← Simp.mkContext { maxSteps := 20000, dsimp := true, decide := false }
        #[thms] (← getSimpCongrTheorems)
      let procs := #[← Simp.getSimprocs]
      IO.FS.writeFile "logs/driver.trace.txt" ""
      let start ← IO.monoMsNow
      let summaries ← summaryExt.getTheorems
      let names := ((← IO.getEnv "EVAL_OPAQUE_CALLEES").getD "").splitOn ","
      let opaqueNames := (names.filter (· != "")).toArray.map fun s =>
        (s.splitOn ".").foldl Name.str Name.anonymous
      compositionalCalleesRef.set #[]
      let compositionalNative := ((← IO.getEnv "EVAL_COMPOSITIONAL_NATIVE").getD "0") == "1"
      let (r, stats) ← ((evaluate body).run { simp := ctx, procs, summaries, opaqueNames, compositionalNative }).run {}
      let specialized ← rewriteNativeProfile r.expr
      let specializedProof ← chain r.proof (specialized.proof?.getD (← mkEqRefl r.expr))
      let r : EvalResult := ⟨specialized.expr, specializedProof⟩
      let nativeFVars := (collectFVars {} r.expr).fvarSet
      for h in hyps do
        if nativeFVars.contains h.fvarId! then throwError "premise leaked into native"
      let val := ShareCommon.shareCommon (← mkLambdaFVars data r.expr)
      let valTy ← inferType val
      IO.FS.writeFile "logs/driver-phase.txt" "native declaration: kernel enter"
      addDecl (.defnDecl {
        name := nn
        levelParams := []
        type := valTy
        value := val
        hints := .abbrev
        safety := .safe })
      enableRealizationsForConst nn
      let ty ← mkForallFVars xs (← mkEq body (mkAppN (mkConst nn) data))
      let pf := ShareCommon.shareCommon (← mkLambdaFVars xs r.proof)
      IO.FS.writeFile "logs/driver-phase.txt" "final equation: kernel enter"
      withOptions (fun o => o.setBool `Elab.async false) <|
        addDecl (.thmDecl { name := tn, levelParams := [], type := ty, value := pf })
      IO.FS.writeFile "logs/driver-phase.txt" "final equation: kernel returned"
      IO.FS.writeFile "logs/driver-finish.txt" "metrics enter"
      let (_, nodes) := (collectNativeNodes r.expr).run {}
      IO.FS.writeFile "logs/driver-finish.txt" "metrics returned"
      let metrics := s!"unique_expr_nodes={nodes.size}\n"
      IO.FS.writeFile s!"logs/{nn}.driver-size.txt" metrics
      logInfo m!"standalone steps={stats.steps} cache_hits={stats.cacheHits} native_nodes={nodes.size} total_ms={(← IO.monoMsNow)-start}"
      if (← IO.getEnv "EVAL_DUMP_NATIVE").isSome then
        let preview ← tryCatchRuntimeEx
          (withCurrHeartbeats <| withTheReader Core.Context (fun c => {c with maxHeartbeats := 2000000}) <|
            withOptions (fun o => o.set `pp.maxSteps (5000 : Nat) |>.set `pp.maxDepth (16 : Nat)) <|
              pure (toString (← ppExpr r.expr)))
          (fun _ => pure "Native preview exceeded its diagnostic budget.")
        IO.FS.writeFile s!"logs/{nn}.driver-nf.txt" preview
      else
        IO.FS.writeFile s!"logs/{nn}.driver-nf.txt" s!"Native declaration: {nn}\n{metrics}Full rendering disabled; set EVAL_DUMP_NATIVE for a bounded preview.\n"
      IO.FS.writeFile "logs/driver-finish.txt" "command returned"
end Stepping
