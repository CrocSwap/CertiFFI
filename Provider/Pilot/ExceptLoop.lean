import Pilot.LoopFrame
namespace StepRuntime

def nativeExceptIntRangeLoop {δ ε σ β : Type} (range : IntRange) (initial : β)
    (body : (i : Int) → i ∈ range → β → ExceptT ε (EStateM δ σ) (ForInStep β))
    (state : σ) : EStateM.Result δ σ (Except ε β) :=
  IntRange.forIn' range initial body state

theorem exceptIntRangeLoop_congr {δ ε σ β : Type} (range : IntRange) (initial : β)
    (original native : (i : Int) → i ∈ range → β → ExceptT ε (EStateM δ σ) (ForInStep β))
    (state : σ)
    (bodyEq : ∀ i membership value current,
      original i membership value current = native i membership value current) :
    IntRange.forIn' range initial original state =
      nativeExceptIntRangeLoop range initial native state := by
  have same : original = native := by
    funext i membership value current
    exact bodyEq i membership value current
  rw [same]
  rfl

theorem exceptIntRange_loop_frame {δ ε σ β ρ : Type}
    (project : σ → ρ) (range : IntRange)
    (body : (i : Int) → i ∈ range → β → ExceptT ε (EStateM δ σ) (ForInStep β))
    (bodyFrame : ∀ i membership value state,
      SuccessFrame project state (body i membership value state))
    (value : β) (index : Int)
    (aligned : (index - range.start) % range.step = 0) :
    ∀ state, SuccessFrame project state
      (IntRange.forIn'.loop range body value index aligned state) := by
  induction value, index, aligned using IntRange.forIn'.loop.induct range with
  | case1 value index aligned member ih =>
    intro state
    rw [IntRange.forIn'.loop.eq_1]
    simp only [dite_eq_left member]
    cases outcome : body index member value state with
    | error error current =>
      simp [Bind.bind, Pure.pure, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure, EStateM.bind,
        EStateM.pure, outcome, SuccessFrame]
    | ok result current =>
      have frame := bodyFrame index member value state
      simp only [outcome, SuccessFrame] at frame
      cases result with
      | error error =>
        simpa [Bind.bind, Pure.pure, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure, EStateM.bind,
          EStateM.pure, outcome, SuccessFrame] using frame
      | ok step =>
        cases step with
        | done value =>
          simpa [Bind.bind, Pure.pure, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure, EStateM.bind,
            EStateM.pure, outcome, SuccessFrame] using frame
        | yield value =>
          have recursive := ih value current
          have final := successFrame_trans project state current _ frame recursive
          simpa [Bind.bind, Pure.pure, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure, EStateM.bind,
            EStateM.pure, outcome] using final
  | case2 value index aligned outside =>
    intro state
    rw [IntRange.forIn'.loop.eq_1]
    simp [dite_eq_right outside, Pure.pure, ExceptT.mk, ExceptT.pure, EStateM.pure, SuccessFrame]

theorem nativeExceptIntRangeLoop_frame {δ ε σ β ρ : Type}
    (project : σ → ρ) (range : IntRange) (initial : β)
    (body : (i : Int) → i ∈ range → β → ExceptT ε (EStateM δ σ) (ForInStep β))
    (bodyFrame : ∀ i membership value state,
      SuccessFrame project state (body i membership value state))
    (state : σ) :
    SuccessFrame project state (nativeExceptIntRangeLoop range initial body state) := by
  simpa only [nativeExceptIntRangeLoop, IntRange.forIn'] using
    exceptIntRange_loop_frame project range body bodyFrame initial range.start (by simp) state

#print axioms exceptIntRangeLoop_congr
#print axioms exceptIntRange_loop_frame
#print axioms nativeExceptIntRangeLoop_frame
end StepRuntime

namespace StepRuntime

def resumeExcept {δ ε σ α β : Type}
    (k : α → ExceptT ε (EStateM δ σ) β)
    (r : EStateM.Result δ σ (Except ε α)) : EStateM.Result δ σ (Except ε β) :=
  match r with
  | .error error current => .error error current
  | .ok (.error error) current => .ok (.error error) current
  | .ok (.ok value) current => k value current

theorem exceptBind_native_cont {δ ε σ α β : Type}
    (x : ExceptT ε (EStateM δ σ) α)
    (original native : α → ExceptT ε (EStateM δ σ) β)
    (state : σ) (result : EStateM.Result δ σ (Except ε α))
    (actionEq : x state = result)
    (continuationEq : ∀ value current, original value current = native value current) :
    ExceptT.bind x original state = resumeExcept native result := by
  have same : original = native := by funext value current; exact continuationEq value current
  subst original
  cases result with
  | error error current =>
    simp [Bind.bind, ExceptT.bind, ExceptT.mk, EStateM.bind, actionEq, resumeExcept]
  | ok value current =>
    cases value <;>
      simp [Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, EStateM.bind, Pure.pure,
        EStateM.pure, actionEq, resumeExcept]

theorem exceptBind_native_frame {δ ε σ α β ρ : Type}
    (project : σ → ρ) (restore : ρ → σ → σ)
    (restoreSelf : ∀ state, restore (project state) state = state)
    (x : ExceptT ε (EStateM δ σ) α)
    (original native : α → ExceptT ε (EStateM δ σ) β)
    (state : σ) (result : EStateM.Result δ σ (Except ε α))
    (actionEq : x state = result) (frame : SuccessFrame project state result)
    (continuationEq : ∀ value current,
      original value (restore (project state) current) = native value current) :
    ExceptT.bind x original state = resumeExcept native result := by
  cases result with
  | error error current =>
    simp [Bind.bind, ExceptT.bind, ExceptT.mk, EStateM.bind, actionEq, resumeExcept]
  | ok value current =>
    have same : project current = project state := frame
    have restored : restore (project state) current = current := by
      rw [← same]; exact restoreSelf current
    cases value with
    | error error =>
      simp [Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, EStateM.bind, Pure.pure,
        EStateM.pure, actionEq, resumeExcept]
    | ok value =>
      simpa [Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, EStateM.bind, actionEq,
        resumeExcept, restored] using continuationEq value current

#print axioms exceptBind_native_cont
#print axioms exceptBind_native_frame
end StepRuntime

namespace StepRuntime
theorem resumeExcept_successFrame {δ ε σ α β ρ : Type} (project : σ → ρ)
    (initial : σ) (continuation : α → ExceptT ε (EStateM δ σ) β)
    (result : EStateM.Result δ σ (Except ε α))
    (frame : SuccessFrame project initial result)
    (continuationFrame : ∀ value current,
      SuccessFrame project current (continuation value current)) :
    SuccessFrame project initial (resumeExcept continuation result) := by
  cases result with
  | error _ _ => trivial
  | ok value current =>
    cases value with
    | error _ => exact frame
    | ok value =>
      exact successFrame_trans project initial current _ frame (continuationFrame value current)
#print axioms resumeExcept_successFrame
end StepRuntime

namespace StepRuntime
theorem resumeExcept_successFrame_fixed {δ ε σ α β ρ : Type} (project : σ → ρ)
    (initial : σ) (continuation : α → ExceptT ε (EStateM δ σ) β)
    (result : EStateM.Result δ σ (Except ε α))
    (frame : SuccessFrame project initial result)
    (continuationFrame : ∀ value current,
      SuccessFrame project initial (continuation value current)) :
    SuccessFrame project initial (resumeExcept continuation result) := by
  cases result with
  | error _ _ => trivial
  | ok value current =>
    cases value with
    | error _ => exact frame
    | ok value => exact continuationFrame value current
#print axioms resumeExcept_successFrame_fixed
end StepRuntime
