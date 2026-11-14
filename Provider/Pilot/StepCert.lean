import Lean
import Pilot.StepRuntime
open Lean Meta Elab Tactic
namespace StepEval
initialize pauseRef : IO.Ref Bool ← IO.mkRef false
initialize matcherRef : IO.Ref (Option Simp.Simproc) ← IO.mkRef none
initialize deltaCacheRef : IO.Ref (Std.HashMap (Name × Nat) Name) ← IO.mkRef {}
initialize opaqueRef : IO.Ref FVarIdSet ← IO.mkRef {}
initialize accessorCacheRef : IO.Ref (Std.HashMap Name Name) ← IO.mkRef {}
initialize projectionCacheRef : IO.Ref (Std.HashMap Name Name) ← IO.mkRef {}
initialize lookupFactCacheRef : IO.Ref (Std.HashMap Expr Expr) ← IO.mkRef {}
initialize lookupTypeCacheRef : IO.Ref (Std.HashMap Expr Simp.Result) ← IO.mkRef {}
initialize lookupWrapperCacheRef : IO.Ref (Std.HashMap Name Bool) ← IO.mkRef {}
def resetLookupFactCaches : MetaM Unit := do
  lookupFactCacheRef.set {}
  lookupTypeCacheRef.set {}
  lookupWrapperCacheRef.set {}

/-- Inspect reducible aliases once; unrelated predicate definitions remain opaque. -/
partial def lookupWrapper (n : Name) : MetaM Bool := do
  if n == ``GetElem?.getElem! then return true
  if let some found := (← lookupWrapperCacheRef.get)[n]? then return found
  lookupWrapperCacheRef.modify (·.insert n false)
  unless (← getReducibilityStatus n) == .reducible do return false
  let .defnInfo info ← getConstInfo n | return false
  for dep in info.value.getUsedConstants do
    if ← lookupWrapper dep then
      lookupWrapperCacheRef.modify (·.insert n true)
      return true
  return false

def containsLookup (ty : Expr) : MetaM Bool := do
  let constants := ty.getUsedConstants
  if constants.contains ``GetElem?.getElem! then return true
  for n in constants do
    if ← lookupWrapper n then return true
  return false

def withOpaque (xs : Array Expr) (action : MetaM α) : MetaM α := do
  let previous ← opaqueRef.get
  opaqueRef.modify fun seen => xs.foldl (fun seen x => seen.insert x.fvarId!) seen
  try action finally opaqueRef.set previous
/-- Close just the free variables used by a single local equation and its proof. -/
def closeLocals (ty pf : Expr) : MetaM (Array Expr) := do
  let lctx ← getLCtx
  let mut used := (collectFVars (collectFVars {} ty) pf).fvarSet
  let mut changed := true
  while changed do
    changed := false
    for d in lctx do
      if used.contains d.fvarId then
        for f in (collectFVars {} d.type).fvarSet.toList do
          unless used.contains f do
            used := used.insert f
            changed := true
  return lctx.foldl (init := #[]) fun xs d => if used.contains d.fvarId then xs.push d.toExpr else xs

/-- Every certificate is a closed declaration, synchronously checked by the kernel. -/
def certify (e : Expr) (r : Simp.Result) (levelParams : List Name := []) : MetaM Simp.Result := do
  if e == r.expr then return r
  let ty ← mkEq e r.expr
  let pf ← match r.proof? with
    | some p => instantiateMVars p
    | none => mkEqRefl e
  let xs ← closeLocals ty pf
  let ty ← instantiateMVars (← mkForallFVars xs ty)
  let pf ← instantiateMVars (← mkLambdaFVars xs pf)
  let n ← mkAuxDeclName `_evalStep
  let d := Declaration.thmDecl { name := n, levelParams, type := ty, value := pf }
  let start ← IO.monoMsNow
  let hb ← IO.getNumHeartbeats
  let limit := ((← IO.getEnv "EVAL_CERT_HB").getD "3000").toNat!
  let opts := (← getOptions).set `maxHeartbeats (hb / 1000 + limit)
  if (← IO.getEnv "EVAL_TRACE").isSome then
    IO.FS.writeFile "logs/current-check.txt" s!"checking {n} head={e.getAppFn.constName?}\n"
  match Kernel.Environment.addDecl (← getEnv).toKernelEnv opts d with
  | .error err =>
    withOptions (fun o => o.setBool `pp.deepTerms true |>.setBool `pp.proofs true |>.set `pp.maxSteps (200000 : Nat)) do
      IO.FS.writeFile "logs/eval-fail.txt" s!"TYPE\n{← ppExpr ty}\nPROOF\n{← ppExpr pf}\n"
    throwError "step certificate failed at {e.getAppFn}: {err.toMessageData opts}"
  | .ok _ => pure ()
  if (← IO.getEnv "EVAL_TRACE").isSome then
    IO.FS.writeFile "logs/current-check.txt" s!"checked {n} head={e.getAppFn.constName?}\n"
  withOptions (fun _ => opts.setBool `Elab.async false) <| addDecl d
  if (← IO.getEnv "EVAL_TRACE").isSome then
    IO.FS.writeFile "logs/current-check.txt" s!"added {n} head={e.getAppFn.constName?}\n"
  let ms := (← IO.monoMsNow) - start
  if (← IO.getEnv "EVAL_TRACE").isSome then
    IO.eprintln s!"eval-step {n} head={e.getAppFn.constName?} kernel_ms={ms}"
  return { r with proof? := some (mkAppN (mkConst n (levelParams.map Level.param)) xs) }

def certifyStep (e : Expr) (s : Simp.Step) : MetaM Simp.Step := do
  -- Structural matcher simprocs compose already checked child certificates.
  -- Checking their lifted equation again would include the pending continuation.
  if let .const n _ := e.getAppFn then
    if (← getMatcherInfo? n).isSome then return s
  match s with
  | .done r => return .done (← certify e r)
  | .visit r => return .visit (← certify e r)
  | .continue (some r) => return .continue (some (← certify e r))
  | .continue none => return s

/-- Check iota with opaque alternatives, then instantiate the pending continuations. -/
def iotaCertificate (e : Expr) : MetaM (Expr × Expr) := do
  let .const fn _ := e.getAppFn | throwError "iotaCertificate: not a matcher"
  let some info ← getMatcherInfo? fn | throwError "iotaCertificate: no matcher info"
  let args := e.getAppArgs
  let firstAlt := args.size - info.numAlts
  let rec go (i : Nat) (args' xs vs : Array Expr) : MetaM (Expr × Expr) := do
    if i < args.size then
      let v := args[i]!
      withLocalDeclD `continuation (← inferType v) fun x =>
        go (i + 1) (args'.set! i x) (xs.push x) (vs.push v)
    else
      let generic := mkAppN e.getAppFn args'
      let .reduced reduced ← reduceMatcher? generic
        | throwError "iotaCertificate: cannot reduce generic matcher"
      let reduced := reduced.headBeta
      let r ← certify generic { expr := reduced }
      let some p := r.proof? | throwError "iotaCertificate: unchanged"
      return (reduced.replaceFVars xs vs, p.replaceFVars xs vs)
  go firstAlt args #[] #[]

/-- Evaluate only syntactically closed numeric terms, retaining a kernel certificate. -/
def closedWhnf (e : Expr) : MetaM Expr := do
  if e.hasFVar || e.hasLooseBVars || e.hasMVar then throwError "closedWhnf: open input"
  if (← IO.getEnv "EVAL_TRACE").isSome then
    let msg ← withOptions (fun o => o.set `pp.maxSteps (2000 : Nat)) do
      pure s!"enter {e.getAppFn.constName?}: {← ppExpr e}"
    IO.FS.writeFile "logs/current-closed.txt" msg
  match Kernel.whnf (← getEnv) (← getLCtx) e with
  | .ok out => return out
  | .error err => throwError "closedWhnf: {err.toMessageData (← getOptions)}"

def syntacticNatLiteral (e : Expr) : Bool :=
  e.isRawNatLit || (e.isAppOfArity ``OfNat.ofNat 3 &&
    e.getAppArgs[0]!.isConstOf ``Nat && e.getAppArgs[1]!.isRawNatLit)

def closedLiteral (e : Expr) (bitVecOfNat : Bool := true) : MetaM (Option Simp.Result) := do
  if e.hasFVar || e.hasLooseBVars || e.hasMVar || e.isRawNatLit then return none
  if e.isAppOfArity ``OfNat.ofNat 3 && e.getAppArgs[1]!.isRawNatLit then return none
  if e.isAppOfArity ``BitVec.ofNat 2 && syntacticNatLiteral e.getAppArgs[0]! &&
      syntacticNatLiteral e.getAppArgs[1]! then
    return none
  if e.isAppOfArity ``Neg.neg 3 then
    let a := e.getAppArgs[2]!
    if a.isAppOfArity ``OfNat.ofNat 3 && a.getAppArgs[1]!.isRawNatLit then return none
  if (← IO.getEnv "EVAL_DEBUG_LITERAL").isSome then
    IO.FS.withFile "logs/literal-debug.txt" .append fun h => h.putStrLn s!"literal-enter {e.getAppFn.constName?}"
  let ty0 ← inferType e
  let ty ← if ty0.isAppOfArity ``BitVec 1 then pure ty0
    else withTransparency .all <| whnf ty0
  let candidate? ← withTransparency .all do
    if ty.isConstOf ``Bool then
      let b ← closedWhnf e
      return if b.isConstOf ``Bool.true || b.isConstOf ``Bool.false then some b else none
    else if ty.isConstOf ``Nat then
      let n ← closedWhnf e
      return (← getNatValue? n).map mkNatLit
    else if ty.isAppOfArity ``BitVec 1 then
      let w := ty.getAppArgs[0]!
      let n ← closedWhnf (mkApp2 (mkConst ``BitVec.toNat) w e)
      match ← getNatValue? n with
      | some v =>
        let w' ← closedWhnf w
        let some width ← getNatValue? w' | return none
        let widthExpr := mkNatLit width
        if bitVecOfNat then
          return some (mkApp2 (mkConst ``BitVec.ofNat) widthExpr (mkNatLit v))
        else return some (← mkNumeral (mkApp (mkConst ``BitVec) widthExpr) v)
      | none => return none
    else if ty.isConstOf ``Int then
      let n ← closedWhnf (mkApp (mkConst ``Int.natAbs) e)
      let pos ← closedWhnf (mkApp (mkConst ``Int.toNat) e)
      match ← getNatValue? n, ← getNatValue? pos with
      | some n, some p =>
        return some (mkIntLit (if n == p then Int.ofNat n else -(Int.ofNat n)))
      | _, _ => return none
    else return none
  let some out := candidate? | return none
  let out ← instantiateMVars out
  if out == e then return none
  if (← IO.getEnv "EVAL_DEBUG_LITERAL").isSome then
    let msg := s!"literal-rewrite {e.getAppFn.constName?} -> {out.getAppFn.constName?}"
    IO.FS.withFile "logs/literal-debug.txt" .append fun h => h.putStrLn msg
  return some (← certify e { expr := out })

/-- Canonicalize closed data inputs before unfolding a monadic callee. -/
def literalInputs (e : Expr) (bitVecOfNat : Bool := true) : MetaM (Option Simp.Result) := do
  if let some r ← closedLiteral e bitVecOfNat then return some r
  unless e.isApp do return none
  if ← isType e then return none
  let args := e.getAppArgs
  let mut fnTy ← inferType e.getAppFn
  for i in [0:args.size] do
    let a := args[i]!
    let .forallE _ _ body _ ← whnf fnTy | return none
    fnTy := body.instantiate1 a
    -- Replacing an index would invalidate later dependent arguments (Fin.val,
    -- GetElem bounds, widths). Whole closed numeric expressions are handled above.
    if body.hasLooseBVar 0 then continue
    let some r ← closedLiteral a bitVecOfNat | continue
    let some p := r.proof? | continue
    let f ← withLocalDeclD `input (← inferType a) fun x =>
      mkLambdaFVars #[x] (mkAppN e.getAppFn (args.set! i x))
    let .forallE _ _ b _ ← whnf (← inferType f) | continue
    if b.hasLooseBVars then continue
    let q ← mkCongrArg f p
    return some { expr := mkAppN e.getAppFn (args.set! i r.expr), proof? := some q }
  return none

/-- Reduce a closed conditional as a function, before applying a symbolic state. -/
def closedIte (e : Expr) : MetaM (Option Simp.Result) := do
  unless e.getAppFn.isConstOf ``ite do return none
  let args := e.getAppArgs
  if args.size < 5 then return none
  let dec := args[2]!
  if dec.hasFVar || dec.hasMVar || dec.hasLooseBVars then return none
  let α := args[0]!
  let (out, pf) ← withLocalDeclD `yesBranch α fun y =>
    withLocalDeclD `noBranch α fun n => do
      let generic := mkAppN e.getAppFn ((args.extract 0 5).set! 3 y |>.set! 4 n)
      let out ← withTransparency .all <| whnf generic
      unless out == y || out == n do throwError "closed conditional did not select a branch"
      let r ← certify generic { expr := out }
      let some pf := r.proof? | throwError "closedIte: unchanged"
      return (out.replaceFVars #[y,n] #[args[3]!,args[4]!],
        pf.replaceFVars #[y,n] #[args[3]!,args[4]!])
  let mut out := out
  let mut pf := pf
  for a in args.extract 5 args.size do
    pf ← mkCongrFun pf a
    out := mkApp out a
  return some { expr := out.headBeta, proof? := some pf }

/-- Unfold a monadic callee at function type, before supplying its state. -/
def deltaBeforeStateCore (e : Expr) : MetaM (Option Simp.Result) := do
  let .const fn lvls := e.getAppFn | return none
  let args := e.getAppArgs
  if args.isEmpty then return none
  let s := args.back!
  let sTy ← whnf (← inferType s)
  unless sTy.isAppOf `Sail.ConcurrencyInterfaceV1.SequentialState do return none
  let ci ← getConstInfo fn
  let some value := ci.value? | return none
  let arity := args.size - 1
  let key := (fn, arity)
  let name? := (← deltaCacheRef.get)[key]?
  let th ← match name? with
    | some n =>
      if (← getEnv).contains n then pure n else pure Name.anonymous
    | none => pure Name.anonymous
  let th ← if !th.isAnonymous then pure th else do
    forallBoundedTelescope ci.type (some arity) (whnfType := true) fun xs _ => do
      let lhs := mkAppN (mkConst fn (ci.levelParams.map Level.param)) xs
      let rhs := (mkAppN value xs).headBeta
      let r ← certify lhs { expr := rhs } ci.levelParams
      let some p := r.proof? | throwError "delta certificate unchanged"
      let n := p.getAppFn.constName!
      deltaCacheRef.modify (·.insert key n)
      return n
  let thInfo ← getConstInfo th
  let handled ← forallTelescope thInfo.type fun xs _ => pure xs.size
  let mut pf := mkAppN (mkConst th lvls) (args.extract 0 handled)
  let some (_, _, rhs) := (← inferType pf).consumeMData.eq? | throwError "delta certificate not equality"
  let mut out := rhs
  -- A polymorphic motive can hide additional function arguments in its result.
  -- Only the declaration's actual binders belong to the generic delta theorem.
  for a in args.extract handled args.size do
    pf ← mkCongrFun pf a
    out := mkApp out a
  return some { expr := out, proof? := some pf }

def unfoldBeforeState (e : Expr) : SimpM (Option Simp.Result) := do
  let .const fn _ := e.getAppFn | return none
  unless (← Simp.getContext).isDeclToUnfold fn do return none
  deltaBeforeStateCore e

/-- Project a needed field through a conditional before traversing either record. -/
def projectConstructor (e : Expr) : MetaM (Option Simp.Result) := do
  let args := e.getAppArgs
  let details? ← match e.getAppFn with
    | .const fn levels => do
      let some info ← getProjectionFnInfo? fn | pure none
      if args.size <= info.numParams then pure none else
        pure (some (fn, levels, info, args[info.numParams]!,
          args.extract (info.numParams + 1) args.size))
    | .proj structName i receiver => do
      let some si := getStructureInfo? (← getEnv) structName | pure none
      let some fn := si.getProjFn? i | pure none
      let some info ← getProjectionFnInfo? fn | pure none
      let ty ← whnf (← inferType receiver)
      let .const _ levels := ty.getAppFn | pure none
      pure (some (fn, levels, info, receiver, args))
    | _ => pure none
  let some (fn, levels, info, receiver, extraArgs) := details? | return none
  let receiver := receiver.consumeMData.headBeta
  unless receiver.getAppFn.isConstOf info.ctorName do return none
  let fields := receiver.getAppArgs
  if fields.size <= info.numParams + info.i then return none
  let ci ← getConstInfo info.ctorName
  let pi ← getConstInfo fn
  unless ci.levelParams.length == pi.levelParams.length do return none
  let cached := (← projectionCacheRef.get)[fn]?
  let th ← match cached with
    | some n => if (← getEnv).contains n then pure n else pure Name.anonymous
    | none => pure Name.anonymous
  let th ← if !th.isAnonymous then pure th else do
    forallBoundedTelescope ci.type (some fields.size) fun xs _ => do
      let lvls := ci.levelParams.map Level.param
      let record := mkAppN (mkConst info.ctorName lvls) xs
      let lhs := mkAppN (mkConst fn lvls) ((xs.extract 0 info.numParams).push record)
      let rhs := xs[info.numParams + info.i]!
      let r ← certify lhs {expr := rhs} ci.levelParams
      let some pf := r.proof? | throwError "constructor projection certificate unchanged"
      let n := pf.getAppFn.constName!
      projectionCacheRef.modify (·.insert fn n)
      pure n
  let mut pf := mkAppN (mkConst th levels) fields
  let mut out := fields[info.numParams + info.i]!
  for a in extraArgs do
    pf ← mkCongrFun pf a
    out := mkApp out a
  return some {expr := out, proof? := some pf}

/-- Project a needed field through a conditional before traversing either record. -/
def projectConditional (e : Expr) : MetaM (Option Simp.Result) := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  let receiver? ← match fn with
    | .const n _ => do
      let some info ← getProjectionFnInfo? n | pure none
      if args.size <= info.numParams then pure none else pure (some (info.numParams, args[info.numParams]!))
    | .proj _ _ receiver => pure (some (args.size, receiver))
    | _ => pure none
  let some (idx, receiver) := receiver? | return none
  let receiver := receiver.consumeMData
  let rf := receiver.getAppFn
  let ra := receiver.getAppArgs
  unless (rf.isConstOf ``ite || rf.isConstOf ``dite) && ra.size == 5 do return none
  let f ← withLocalDeclD `recordValue (← inferType receiver) fun v => do
    let body := match fn with
      | .proj n i _ => mkAppN (.proj n i v) args
      | _ => mkAppN fn (args.set! idx v)
    mkLambdaFVars #[v] body
  let lemma := if rf.isConstOf ``dite then ``apply_dite else ``apply_ite
  let pf ← mkAppM lemma #[f,ra[1]!,ra[3]!,ra[4]!]
  let some (_, _, out) := (← inferType pf).eq? | return none
  return some (← certify e { expr := out, proof? := some pf })

/-- Make an in-bounds lookup fact usable after the evaluator exposes its proof-bounded form. -/
def normalizeLookupFact (fact : Expr) : MetaM Expr := do
  if let some result := (← lookupFactCacheRef.get)[fact]? then
    if result == fact then return fact
    let context ← getLCtx
    let env ← getEnv
    if (collectFVars {} result).fvarSet.toList.all (fun id => (context.find? id).isSome) &&
        result.getUsedConstants.all env.contains then return result
  let ty ← inferType fact
  let cached? := (← lookupTypeCacheRef.get)[ty]?
  let cached? ← match cached? with
    | none => pure none
    | some r => do
      match r.proof? with
      | none => pure (some r)
      | some pf =>
        let context ← getLCtx
        let env ← getEnv
        if (collectFVars {} pf).fvarSet.toList.all (fun id => (context.find? id).isSome) &&
            pf.getUsedConstants.all env.contains then pure (some r) else pure none
  let r ← match cached? with
    | some r => pure r
    | none => do
      let r ← if ← containsLookup ty then do
        let mut thms : SimpTheorems := {}
        thms ← thms.addConst ``getElem!_pos
        let ctx ← Simp.mkContext {maxSteps := 2000, dsimp := true}
          #[thms] (← getSimpCongrTheorems)
        let (r, _) ← Simp.main ty ctx (methods := Simp.mkDefaultMethodsCore #[← Simp.getSimprocs])
        if r.expr == ty then pure {expr := ty} else certify ty r
      else pure {expr := ty}
      lookupTypeCacheRef.modify (·.insert ty r)
      pure r
  let result ← match r.proof? with
    | none => pure fact
    | some pf => mkEqMP pf fact
  lookupFactCacheRef.modify (·.insert fact result)
  return result

/-- Remove record/projection scaffolding without evaluating scalar field data. -/
def recordProjectionSteps (e : Expr) : MetaM Simp.Result := do
  let mut thms : SimpTheorems := {}
  thms ← thms.addConst ``ite_self
  thms ← thms.addConst ``StepRuntime.merge_dite
  for decl in (← getLCtx) do
    unless decl.isImplementationDetail do
      if ← isProp decl.type then
        thms ← thms.add (.fvar decl.fvarId) #[] decl.toExpr
        let normalized ← normalizeLookupFact decl.toExpr
        if normalized != decl.toExpr then
          thms ← thms.add (.other (← mkFreshUserName `lookupFact)) #[] normalized
  let ctx ← Simp.mkContext { maxSteps := 20000, dsimp := false, beta := true, zeta := true, iota := false, proj := false }
    #[thms] (← getSimpCongrTheorems)
  let base := Simp.mkDefaultMethodsCore #[]
  let pre : Simp.Simproc := fun value => do
    if let some r ← Simp.rewrite? value thms.post thms.erased "record_local" false then
      return .visit r
    if let some r ← projectConstructor value then return .visit r
    if let some r ← projectConditional value then return .visit r
    let head := value.getAppFn
    let scaffold : Bool ← match value with
      | .lam .. | .letE .. | .mdata .. => pure true
      | _ => do
        if head.isLambda || head.isConstOf ``ite || head.isConstOf ``dite then pure true
        else
          match head with
          | .const n _ => do
            match ← getConstInfo n with
            | .ctorInfo ci => pure (ci.induct != ``Fin && (getStructureInfo? (← getEnv) ci.induct).isSome)
            | _ => pure false
          | _ => pure false
    unless scaffold do return .done {expr := value}
    base.pre value
  let (r, _) ← Simp.main e ctx (methods := {base with pre})
  return r

/-- Rewrite a symbolic vector argument before an indexer reduces its bounds. -/
def shapeIndexerInput (e : Expr) : MetaM (Option Simp.Result) := do
  unless e.getAppFn.isConstOf ``GetElem?.getElem! do return none
  let args := e.getAppArgs
  let mut fnTy ← inferType e.getAppFn
  for i in [0:args.size] do
    let a := args[i]!
    let .forallE _ ty body _ ← whnf fnTy | return none
    fnTy := body.instantiate1 a
    if body.hasLooseBVar 0 then continue
    unless ty.isAppOf ``Vector do continue
    let r ← recordProjectionSteps a
    if r.expr == a then continue
    let pf ← match r.proof? with
      | some pf => pure pf
      | none => mkExpectedTypeHint (← mkEqRefl a) (← mkEq a r.expr)
    let f ← withLocalDeclD `vectorInput ty fun v =>
      mkLambdaFVars #[v] (mkAppN e.getAppFn (args.set! i v))
    return some {expr := mkAppN e.getAppFn (args.set! i r.expr), proof? := some (← mkCongrArg f pf)}
  return none

/-- A definition which returns a Boolean constant needs no argument reduction. -/
def unfoldFieldAccessor (e : Expr) : MetaM (Option Simp.Result) := do
  let .const fn levels := e.getAppFn | return none
  let .str _ field := fn | return none
  unless (`ArmFull.Functions).isPrefixOf fn && field.startsWith "_get_" do return none
  let ci ← getConstInfo fn
  let some value := ci.value? | return none
  let cached := (← accessorCacheRef.get)[fn]?
  let th ← match cached with
    | some n => if (← getEnv).contains n then pure n else pure Name.anonymous
    | none => pure Name.anonymous
  let th ← if !th.isAnonymous then pure th else do
    let c := mkConst fn (ci.levelParams.map Level.param)
    let r ← certify c {expr := value} ci.levelParams
    let some pf := r.proof? | throwError "field accessor certificate unchanged"
    let n := pf.getAppFn.constName!
    accessorCacheRef.modify (·.insert fn n)
    pure n
  let mut pf := mkConst th levels
  for a in e.getAppArgs do pf ← mkCongrFun pf a
  let out := (mkAppN (value.instantiateLevelParams ci.levelParams levels) e.getAppArgs).headBeta
  return some {expr := out, proof? := some pf}

/-- A definition which returns a Boolean constant needs no argument reduction. -/
def constantBoolean (e : Expr) : MetaM (Option Simp.Result) := do
  let .const n levels := e.getAppFn | return none
  let info ← getConstInfo n
  let some value := info.value? | return none
  let out := (mkAppN (value.instantiateLevelParams info.levelParams levels) e.getAppArgs).headBeta.consumeMData
  unless out.isConstOf ``Bool.true || out.isConstOf ``Bool.false do return none
  return some (← certify e {expr := out})

/-- Certify local redexes before simp lifts their equations into continuations. -/
def simpSteps (e : Expr) (ctx : Simp.Context) (procs : Simp.SimprocsArray)
    (discharge? : Option Simp.Discharge)
    (projection? : Option (Expr → MetaM (Option Simp.Result)) := none) : MetaM (Simp.Result × Simp.Stats) := do
  pauseRef.set false
  let m := match discharge? with
    | none => Simp.mkDefaultMethodsCore procs
    | some d => Simp.mkMethods procs d (wellBehavedDischarge := false)
  let pre : Simp.Simproc := fun e => do
    if (← IO.getEnv "EVAL_TRACE").isSome then
      IO.FS.writeFile "logs/current-simp.txt" s!"pre {e.getAppFn.constName?} args={e.getAppNumArgs} fv={e.hasFVar}"
    if ← pauseRef.get then return .done { expr := e }
    -- A proof-bounded lookup at a symbolic index is already a data value.
    -- Expanding its implementation would inspect arbitrary oracle histories.
    if e.getAppFn.isConstOf ``GetElem.getElem && e.getAppNumArgs == 8 &&
        (e.getAppArgs[6]!.hasFVar || e.getAppArgs[6]!.hasLooseBVars) then
      return .done { expr := e }
    -- A labelled oracle draw is symbolic data. Its label can carry the entire
    -- execution history; traversing it cannot determine the arbitrary value.
    if e.getAppFn.isConstOf ``Sail.ConcurrencyInterfaceV1.ChoiceSource.chooseAt then
      return .done { expr := e }
    if let .fvar id := e.getAppFn.consumeMData then
      if (← opaqueRef.get).contains id then return .done { expr := e }
    -- Field-specific premises must fire before an accessor is unfolded;
    -- otherwise a named getter premise disappears behind its bit extraction.
    let getter := match e.getAppFn with
      | .const (.str _ field) _ => field.startsWith "_get_"
      | _ => false
    if getter then
      for thms in ctx.simpTheorems do
        if let some r ← Simp.rewrite? e thms.post thms.erased "profile_first" false then
          return .visit (← certify e r)
    if let some r ← shapeIndexerInput e then
      pauseRef.set true
      return .done r
    if let some project := projection? then
      if let some r ← project e then return .done r
    if let some r ← projectConstructor e then
      return .visit r
    if let some r ← unfoldFieldAccessor e then
      pauseRef.set true
      return .done r
    if let some r ← projectConditional e then
      pauseRef.set true
      return .done r
    if let some r ← closedIte e then
      pauseRef.set true
      return .done r
    if let some r ← constantBoolean e then return .visit r
    if let .const fn _ := e.getAppFn then
      if let some info ← getMatcherInfo? fn then
        let args := e.getAppArgs
        let di := info.numParams + 1
        if info.numDiscrs == 1 && args.size == di + 1 + info.numAlts then
          let dTy ← whnf (← inferType args[di]!)
          if dTy.isAppOf ``EStateM.Result then
            if let some proc ← matcherRef.get then
              match ← proc e with
              | .continue none => pure ()
              | step => return step
        -- A scalar matcher may return a state-taking computation and then be
        -- applied to a symbolic state. Check the closed scalar match BEFORE
        -- supplying that state; otherwise kernel Nat arithmetic sees the state.
        let arity := di + 1 + info.numAlts
        if info.numDiscrs == 1 && args.size >= arity &&
            !args[di]!.hasFVar && !args[di]!.hasLooseBVars && !args[di]!.hasMVar then
          let matcherApp := mkAppN e.getAppFn (args.extract 0 arity)
          if let .reduced _ ← reduceMatcher? matcherApp then
            let (out, pf) ← iotaCertificate matcherApp
            let mut out := out
            let mut pf := pf
            for a in args.extract arity args.size do
              pf ← mkCongrFun pf a
              out := mkApp out a
            pauseRef.set true
            return .done { expr := out.headBeta, proof? := some pf }
    if let some r ← literalInputs e ctx.config.bitVecOfNat then return .visit r
    if let some r ← unfoldBeforeState e then
      pauseRef.set true
      return .done r
    if (← IO.getEnv "EVAL_TRACE").isSome then
      let headKind := match e.getAppFn.consumeMData with
        | .fvar id => s!"fvar {id.name}"
        | .lam .. => "lambda"
        | .letE .. => "let"
        | .proj n i _ => s!"proj {n}.{i}"
        | _ => "other"
      IO.FS.writeFile "logs/current-simp.txt" s!"default-pre {e.getAppFn.constName?} kind={headKind} args={e.getAppNumArgs} fv={e.hasFVar}"
    let s ← m.pre e
    certifyStep e s
  let post : Simp.Simproc := fun e => do
    if ← pauseRef.get then return .done { expr := e }
    if (← IO.getEnv "EVAL_TRACE").isSome then
      IO.FS.writeFile "logs/current-simp.txt" s!"default-post {e.getAppFn.constName?} args={e.getAppNumArgs} fv={e.hasFVar}"
      if e.getAppFn.isConstOf ``GetElem.getElem then
        withOptions (fun o => o.set `pp.maxSteps (1000 : Nat) |>.set `pp.maxDepth (10 : Nat)) do
          IO.FS.writeFile "logs/indexer-frontier.txt" s!"{← ppExpr e}"
    let s ← m.post e
    certifyStep e s
  try
    Simp.main e ctx (methods := { m with pre := pre, post := post })
  finally
    pauseRef.set false
end StepEval

/-- Rewrite profile facts before the first kernel reduction; certify the resulting equation. -/
elab "config_eval" "[" hs:Lean.Parser.Tactic.rwRule,* "]" : tactic => do
  let start ← IO.monoMsNow
  unless hs.getElems.isEmpty do
    evalTactic (← `(tactic| rw [$hs,*]))
  let g ← getMainGoal
  g.withContext do
    let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).consumeMData.eq?
      | throwError "config_eval expects an equation: {← g.getType}"
    let r ← StepEval.certify lhs { expr := rhs }
    let some p := r.proof? | throwError "config_eval: unchanged target"
    g.assign p
  replaceMainGoal []
  logInfo m!"config_eval total_ms={(← IO.monoMsNow) - start}"
