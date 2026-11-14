import TagCheckFrames.Loops
open Lean Meta Elab Tactic
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace HeapScalarTagCheck.Automation
open TagCheckFrames
theorem let_frame {α β : Type} (value : α) (body : α → SailM β)
    (frame : ∀ argument, Preserves (body argument)) : Preserves (let argument := value; body argument) :=
  frame value

partial def solveFrame (fuel : Nat) : TacticM Unit := do
  let remaining ← (← getGoals).filterM (fun g => return !(← g.isAssigned))
  setGoals remaining
  if remaining.isEmpty then return
  if fuel == 0 then throwError "frame fuel exhausted"
  let g ← getMainGoal
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    if target.isForall then
      evalTactic (← `(tactic| intro))
      solveFrame (fuel-1)
      return
    let p := target.getAppArgs.back!
    let reduced := p.headBeta
    if reduced != p then
      let st ← mkAppM ``Preserves #[reduced]
      let ng ← g.replaceTargetDefEq st
      replaceMainGoal [ng]
      solveFrame (fuel-1)
      return
    if p.isLet then
      let valueType := p.letType!.getAppFn.constName?.getD .anonymous
      let pureValue := [``BitVec, ``Fin, ``Nat, ``Int, ``Bool].contains valueType
      if pureValue && p.letValue!.hasFVar then
        let .letE binderName binderType value body _ := p
          | throwError "expected a let expression"
        let bodyFunction := mkLambda binderName .default binderType body
        let lemma ← mkAppM ``let_frame #[value, bodyFunction]
        replaceMainGoal (← g.apply lemma)
      else
        let reduced := p.letBody!.instantiate1 p.letValue!
        let statement ← mkAppM ``Preserves #[reduced]
        replaceMainGoal [← g.replaceTargetDefEq statement]
      solveFrame (fuel-1)
      return
    let head := p.getAppFn
    let nm := head.constName?.getD .anonymous
    if nm == ``Bind.bind || nm == ``EStateM.bind then
      let args := p.getAppArgs
      let operands := #[args[args.size-2]!, args[args.size-1]!]
      let lemma ← try mkAppM ``bind_frame operands catch _ => mkAppM ``bind_except_frame operands
      let gs ← g.apply lemma
      replaceMainGoal gs
    else if nm == ``Pure.pure || nm == ``EStateM.pure then
      evalTactic (← `(tactic| exact pure_frame _))
    else if nm == ``Functor.map || nm == ``EStateM.map then
      let args := p.getAppArgs
      let operands := #[args[args.size-2]!, args[args.size-1]!]
      let lemma ← try mkAppM ``map_frame operands catch _ => mkAppM ``map_except_frame operands
      let gs ← g.apply lemma
      replaceMainGoal gs
    else if nm == ``ite then
      evalTactic (← `(tactic| apply ite_frame))
    else if nm == ``PreSail.readBytes then
      evalTactic (← `(tactic| exact readBytes_frame _ _))
    else if nm == ``PreSail.readReg then
      evalTactic (← `(tactic| exact read_frame _))
    else if nm == ``PreSail.writeReg then
      evalTactic (← `(tactic| exact write_frame _ _))
    else if nm == ``PreSail.chooseAt then
      evalTactic (← `(tactic| exact chooseAt_frame _ _))
    else if nm == ``PreSail.choose then
      evalTactic (← `(tactic| exact choose_frame _))
    else if nm == ``PreSail.occLabel then
      evalTactic (← `(tactic| apply occ_frame; decide))
    else if nm == ``MonadExcept.throw then
      evalTactic (← `(tactic| exact throw_frame _))
    else if nm == ``SailME.run || nm == ``PreSail.PreSailME.run then
      evalTactic (← `(tactic| apply run_frame))
    else if nm == ``ExceptT.lift then
      evalTactic (← `(tactic| apply lift_frame))
    else if nm == ``List.forM then
      evalTactic (← `(tactic| first | apply listForM_frame | apply listForM_except_frame))
    else if nm == ``ForIn.forIn then
      evalTactic (← `(tactic| first | apply forIn_range_frame | apply forIn_range_except_frame))
    else if nm == ``IntRange.forIn' then
      evalTactic (← `(tactic| first | apply range_frame | apply range_except_frame))
    else if nm == ``sailUntilFuelM then
      evalTactic (← `(tactic| first | apply until_frame | apply until_except_frame))
    else if nm == ``sailWhileFuelM then
      evalTactic (← `(tactic| first | apply while_frame | apply while_except_frame))
    else if head.isConst && (`ArmFull.Functions).isPrefixOf nm && (nm.toString.splitOn "match").length == 1 then
      let derived := `HeapScalarTagCheck.Derived ++ nm
      if !(← getEnv).contains derived then
        let info ← getConstInfo nm
        let c := mkConst nm (info.levelParams.map Level.param)
        let saved ← getGoals
        let (ty, val) ← forallTelescope info.type fun xs _ => do
          let statement ← mkAppM ``Preserves #[mkAppN c xs]
          let fresh ← mkFreshExprMVar statement
          setGoals [fresh.mvarId!]
          let p0 := mkAppN c xs
          let some expanded ← unfoldDefinition? p0 (ignoreTransparency := true)
            | throwError "cannot unfold cached function {nm}"
          let st ← mkAppM ``Preserves #[expanded]
          let ng ← fresh.mvarId!.replaceTargetDefEq st
          setGoals [ng]
          solveFrame (fuel-1)
          let proof ← instantiateMVars fresh
          if proof.hasMVar then throwError "unsolved cached frame {nm}"
          return (← mkForallFVars xs statement, ← mkLambdaFVars xs proof)
        addDecl (.thmDecl {name := derived, levelParams := info.levelParams, type := ty, value := val})
        setGoals saved
        logInfo m!"derived {nm}"
      let proof := mkAppN (mkConst derived head.constLevels!) p.getAppArgs
      g.assign proof
      replaceMainGoal []
    else if head.isConst then
      logInfo m!"unfold {nm}"
      try
        evalTactic (← `(tactic| split))
      catch _ =>
        if nm == ``Except.rec then
          let major := p.getAppArgs.back!
          let gs ← g.cases major.fvarId!
          replaceMainGoal (gs.toList.map (·.mvarId))
        else
          let some expanded ← unfoldDefinition? p (ignoreTransparency := true)
            | throwError "cannot unfold {nm}"
          let st ← mkAppM ``Preserves #[expanded]
          let ng ← g.replaceTargetDefEq st
          replaceMainGoal [ng]
    else if head.isLambda then
      evalTactic (← `(tactic| (intro s a t h; cases h <;> exact ⟨rfl, by simp [Std.ExtHashMap.getD_insert]⟩)))
    else if head.isProj then
      try
        evalTactic (← `(tactic| apply lift_frame))
      catch _ =>
        let .proj _ _ _ := head | throwError "expected projection"
        let reduced ← whnf head
        let expanded := (mkAppN reduced p.getAppArgs).headBeta
        let st ← mkAppM ``Preserves #[expanded]
        let ng ← g.replaceTargetDefEq st
        replaceMainGoal [ng]
    else
      throwError "unsupported frame {target} (head {head})"
    let gs ← getGoals
    for goal in gs do
      setGoals [goal]
      solveFrame (fuel-1)
elab "scalar_oracle_frame" : tactic => solveFrame 10000
end HeapScalarTagCheck.Automation
