import Bridge.CruxCore
import Lean
import NativeMteTagCheck.Transport
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace NativeTagCheck.PrimitiveFrames
abbrev State := NativeMteTagCheck.State
abbrev Delta (s t : State) := NativeMteTagCheck.ChoiceDelta s t 0
def Preserves {α : Type} (p : SailM α) : Prop :=
  ∀ s a t, p s = .ok a t → Delta s t

theorem pure_frame {α : Type} (a : α) : Preserves (pure a) := by
  intro s v t h
  cases h
  exact NativeMteTagCheck.choice_delta_refl s

theorem bind_frame {α β : Type} (p : SailM α) (k : α → SailM β)
    (hp : Preserves p) (hk : ∀ a, Preserves (k a)) : Preserves (p >>= k) := by
  intro s b u run
  simp only [Bind.bind, EStateM.bind] at run
  cases h : p s with
  | error e t => simp [h] at run
  | ok a t =>
    rw [h] at run
    have hd := NativeMteTagCheck.choice_delta_trans (hp s a t h) (hk a t b u run)
    simpa using hd

theorem ite_frame {α : Type} (b : Prop) [Decidable b] (p q : SailM α)
    (hp : b → Preserves p) (hq : ¬b → Preserves q) : Preserves (if b then p else q) := by
  split <;> simp_all

theorem read_frame {α : Type} (r : RegisterRef Regs α) : Preserves (readReg r) := by
  intro s a t h
  cases h
  exact NativeMteTagCheck.choice_delta_refl s

theorem occ_frame (n : Nat) (hne : n ≠ 1354) : Preserves (occLabel n : SailM ChoiceLabel) := by
  intro s a t h
  cases h
  exact ⟨rfl, by simp [Std.ExtHashMap.getD_insert, hne, Ne.symm hne]⟩

theorem map_frame {α β : Type} (f : α → β) (p : SailM α)
    (hp : Preserves p) : Preserves (f <$> p) := by
  intro s a t h
  cases hr : p s with
  | error e u => simp [Functor.map, EStateM.map, hr] at h
  | ok b u =>
    simp only [Functor.map, EStateM.map, hr] at h
    cases h
    exact hp s b t hr

theorem write_frame {α : Type} (r : RegisterRef Regs α) (a : α) : Preserves (writeReg r a) := by
  intro s v t h
  cases h
  exact NativeMteTagCheck.choice_delta_refl s

theorem chooseAt_frame (p : Sail.Primitive) (l : ChoiceLabel) :
    Preserves (PreSail.chooseAt p l : SailM p.reflect) := by
  intro s a t h
  cases h
  exact NativeMteTagCheck.choice_delta_refl s

theorem choose_frame (p : Sail.Primitive) :
    Preserves (PreSail.choose p : SailM p.reflect) := by
  intro s a t h
  cases h
  exact ⟨rfl, by simp⟩

theorem throw_frame {α : Type} (e : Error exception) : Preserves (throw e : SailM α) := by
  intro s a t h
  contradiction
theorem bind_except_frame {ε α β : Type} (p : ExceptT ε SailM α) (k : α → ExceptT ε SailM β)
    (hp : Preserves p) (hk : ∀ a, Preserves (k a)) : Preserves (p >>= k : ExceptT ε SailM β) := by
  change Preserves (EStateM.bind p (ExceptT.bindCont k))
  apply bind_frame _ _ hp
  intro a
  cases a with
  | error e => exact pure_frame _
  | ok a => exact hk a
theorem lift_frame {ε α : Type} (p : SailM α) (hp : Preserves p) :
    Preserves (ExceptT.lift p : ExceptT ε SailM α) := by
  exact map_frame Except.ok p hp
theorem run_frame {α : Type} (p : SailME α α) (hp : Preserves p) :
    Preserves (SailME.run p) := by
  unfold SailME.run PreSail.PreSailME.run
  apply bind_frame _ _ hp
  intro x
  cases x with
  | ok a => exact pure_frame a
  | error e =>
    cases e with
    | inl e => exact throw_frame e
    | inr a => exact pure_frame a
theorem map_except_frame {ε α β : Type} (f : α → β) (p : ExceptT ε SailM α)
    (hp : Preserves p) : Preserves (f <$> p : ExceptT ε SailM β) := by
  change Preserves (EStateM.bind p _)
  apply bind_frame _ _ hp
  intro a
  cases a <;> exact pure_frame _
theorem readBytes_frame (n addr : Nat) : Preserves (PreSail.readBytes n addr : SailM _) := by
  intro s a t h
  rcases PreSail.readBytes_state (c := oracleChoiceSource) (ue := exception) n addr s with ⟨v,hv⟩ | ⟨e,he⟩
  · rw [hv] at h
    cases h
    exact NativeMteTagCheck.choice_delta_refl s
  · rw [he] at h
    contradiction
end NativeTagCheck.PrimitiveFrames

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeTagCheck.PrimitiveFrames
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem until_frame {α : Type} (fuel : Nat) (cond : α → SailM Bool)
    (init : α) (f : α → SailM α) (hc : ∀ a, Preserves (cond a))
    (hf : ∀ a, Preserves (f a)) :
    Preserves (sailUntilFuelM (m := SailM) fuel cond init f) := by
  induction fuel generalizing init with
  | zero =>
    intro s a t h
    contradiction
  | succ fuel ih =>
    unfold sailUntilFuelM
    apply bind_frame _ _ (hf init)
    intro x
    apply bind_frame _ _ (hc x)
    intro b
    split
    · exact pure_frame _
    · exact ih x

theorem until_except_frame {ε α : Type} (fuel : Nat) (cond : α → ExceptT ε SailM Bool)
    (init : α) (f : α → ExceptT ε SailM α) (hc : ∀ a, Preserves (cond a))
    (hf : ∀ a, Preserves (f a)) :
    Preserves (sailUntilFuelM (m := ExceptT ε SailM) fuel cond init f) := by
  induction fuel generalizing init with
  | zero =>
    intro s a t h
    contradiction
  | succ fuel ih =>
    unfold sailUntilFuelM
    apply bind_except_frame _ _ (hf init)
    intro x
    apply bind_except_frame _ _ (hc x)
    intro b
    split
    · exact pure_frame _
    · exact ih x
theorem while_frame {α : Type} (fuel : Nat) (cond : α → SailM Bool)
    (init : α) (f : α → SailM α) (hc : ∀ a, Preserves (cond a))
    (hf : ∀ a, Preserves (f a)) :
    Preserves (sailWhileFuelM (m := SailM) fuel cond init f) := by
  induction fuel generalizing init with
  | zero => intro s a t h; contradiction
  | succ fuel ih =>
    unfold sailWhileFuelM
    apply bind_frame _ _ (hc init)
    intro b
    split
    · apply bind_frame _ _ (hf init)
      intro x
      exact ih x
    · exact pure_frame _

theorem while_except_frame {ε α : Type} (fuel : Nat) (cond : α → ExceptT ε SailM Bool)
    (init : α) (f : α → ExceptT ε SailM α) (hc : ∀ a, Preserves (cond a))
    (hf : ∀ a, Preserves (f a)) :
    Preserves (sailWhileFuelM (m := ExceptT ε SailM) fuel cond init f) := by
  induction fuel generalizing init with
  | zero => intro s a t h; contradiction
  | succ fuel ih =>
    unfold sailWhileFuelM
    apply bind_except_frame _ _ (hc init)
    intro b
    split
    · apply bind_except_frame _ _ (hf init)
      intro x
      exact ih x
    · exact pure_frame _
theorem range_frame {β : Type} (range : IntRange) (init : β)
    (f : (i : Int) → i ∈ range → β → SailM (ForInStep β))
    (hf : ∀ i h b, Preserves (f i h b)) :
    Preserves (IntRange.forIn' (m := SailM) range init f) := by
  unfold IntRange.forIn'
  have loopFrame : ∀ b i h, Preserves (IntRange.forIn'.loop (m := SailM) range f b i h) := by
    intro b i h
    induction b, i, h using IntRange.forIn'.loop.induct range with
    | case1 b i hs inside ih =>
      rw [IntRange.forIn'.loop]
      simp only [dif_pos inside]
      apply bind_frame _ _ (hf i inside b)
      intro step
      cases step with
      | done b => exact pure_frame _
      | yield b => exact ih b
    | case2 b i hs outside =>
      rw [IntRange.forIn'.loop]
      simp only [dif_neg outside]
      exact pure_frame _
  exact loopFrame _ _ _

theorem range_except_frame {ε β : Type} (range : IntRange) (init : β)
    (f : (i : Int) → i ∈ range → β → (ExceptT ε SailM) (ForInStep β))
    (hf : ∀ i h b, Preserves (f i h b)) :
    Preserves (IntRange.forIn' (m := (ExceptT ε SailM)) range init f) := by
  unfold IntRange.forIn'
  have loopFrame : ∀ b i h, Preserves (IntRange.forIn'.loop (m := (ExceptT ε SailM)) range f b i h) := by
    intro b i h
    induction b, i, h using IntRange.forIn'.loop.induct range with
    | case1 b i hs inside ih =>
      rw [IntRange.forIn'.loop]
      simp only [dif_pos inside]
      apply bind_except_frame _ _ (hf i inside b)
      intro step
      cases step with
      | done b => exact pure_frame _
      | yield b => exact ih b
    | case2 b i hs outside =>
      rw [IntRange.forIn'.loop]
      simp only [dif_neg outside]
      exact pure_frame _
  exact loopFrame _ _ _
theorem forIn_range_frame {β : Type} (range : IntRange) (init : β)
    (f : Int → β → SailM (ForInStep β)) (hf : ∀ i b, Preserves (f i b)) :
    Preserves (ForIn.forIn range init f : SailM β) := by
  apply range_frame
  intro i h b
  exact hf i b

theorem forIn_range_except_frame {ε β : Type} (range : IntRange) (init : β)
    (f : Int → β → (ExceptT ε SailM) (ForInStep β)) (hf : ∀ i b, Preserves (f i b)) :
    Preserves (ForIn.forIn range init f : (ExceptT ε SailM) β) := by
  apply range_except_frame
  intro i h b
  exact hf i b
theorem listForM_frame {α : Type} (xs : List α) (f : α → SailM PUnit)
    (hf : ∀ a, Preserves (f a)) : Preserves (List.forM xs f) := by
  induction xs with
  | nil => exact pure_frame _
  | cons a xs ih =>
    simp only [List.forM]
    apply bind_frame _ _ (hf a)
    intro _
    exact ih

theorem listForM_except_frame {ε α : Type} (xs : List α) (f : α → (ExceptT ε SailM) PUnit)
    (hf : ∀ a, Preserves (f a)) : Preserves (List.forM (m := ExceptT ε SailM) xs f) := by
  induction xs with
  | nil => exact pure_frame _
  | cons a xs ih =>
    simp only [List.forM]
    apply bind_except_frame _ _ (hf a)
    intro _
    exact ih
end NativeTagCheck.PrimitiveFrames

open Lean Meta Elab Tactic
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeTagCheck.PrimitiveFrames
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
      let reduced := p.letBody!.instantiate1 p.letValue!
      let st ← mkAppM ``Preserves #[reduced]
      let ng ← g.replaceTargetDefEq st
      replaceMainGoal [ng]
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
      let derived := `NativeTagCheck.PrimitiveFrames.Derived ++ nm
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
        let .proj _ _ e := head | throwError "expected projection"
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
elab "oracle_frame" : tactic => solveFrame 10000
end NativeTagCheck.PrimitiveFrames

namespace NativeTagCheck.PrimitiveFrames
open ArmBridge.Draft ArmBridge.CruxCore NativeMteTagCheck
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
set_option Elab.async false
theorem res_source {α : Type} (p : SailM α) (frame : Preserves p) (s : NativeState) :
    (resCS s (p s)).1 = s.choiceState.1 := by
  cases run : p s with
  | error error t => rfl
  | ok value t => exact (frame s value t run).1
theorem res_counter {α : Type} (p : SailM α) (frame : Preserves p) (s : NativeState) :
    (resCO s (p s)).getD 1354 0 = s.choiceOcc.getD 1354 0 := by
  cases run : p s with
  | error error t => rfl
  | ok value t => simpa only [resCO, Nat.add_zero] using (frame s value t run).2
theorem spe_pre_preserves : Preserves (SPEPreExecution ()) := by oracle_frame
theorem ss_advance_preserves : Preserves (SSAdvance ()) := by oracle_frame
theorem spe_cycle_preserves : Preserves (SPECycle ()) := by oracle_frame
#print axioms spe_pre_preserves
#print axioms ss_advance_preserves
#print axioms spe_cycle_preserves
end NativeTagCheck.PrimitiveFrames
