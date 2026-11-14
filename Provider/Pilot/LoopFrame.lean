import Pilot.StepRuntime
namespace StepRuntime

def SuccessFrame {ε σ α ρ : Type} (project : σ → ρ) (initial : σ)
    (result : EStateM.Result ε σ α) : Prop :=
  match result with
  | .ok _ current => project current = project initial
  | .error _ _ => True

theorem successFrame_trans {ε σ α ρ : Type} (project : σ → ρ)
    (initial middle : σ) (result : EStateM.Result ε σ α)
    (same : project middle = project initial)
    (frame : SuccessFrame project middle result) :
    SuccessFrame project initial result := by
  cases result with
  | ok value current => exact frame.trans same
  | error error current => trivial

theorem intRange_loop_frame {ε σ β ρ : Type}
    (project : σ → ρ) (range : IntRange)
    (body : (index : Int) → index ∈ range → β → EStateM ε σ (ForInStep β))
    (bodyFrame : ∀ index membership value state,
      SuccessFrame project state (body index membership value state))
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
      simp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, outcome, SuccessFrame]
    | ok step current =>
      have frame := bodyFrame index member value state
      simp only [outcome, SuccessFrame] at frame
      cases step with
      | done value =>
        simpa [Bind.bind, Pure.pure, EStateM.bind, outcome, EStateM.pure, SuccessFrame] using frame
      | yield value =>
        have recursive := ih value current
        have final := successFrame_trans project state current _ frame recursive
        simpa [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, outcome] using final
  | case2 value index aligned outside =>
    intro state
    rw [IntRange.forIn'.loop.eq_1]
    simp [dite_eq_right outside, Pure.pure, EStateM.pure, SuccessFrame]

theorem nativeIntRangeLoop_frame {ε σ β ρ : Type}
    (project : σ → ρ) (range : IntRange) (initial : β)
    (body : (index : Int) → index ∈ range → β → EStateM ε σ (ForInStep β))
    (bodyFrame : ∀ index membership value state,
      SuccessFrame project state (body index membership value state))
    (state : σ) :
    SuccessFrame project state (nativeIntRangeLoop range initial body state) := by
  simpa only [nativeIntRangeLoop, IntRange.forIn'] using
    intRange_loop_frame project range body bodyFrame initial range.start (by simp) state

theorem bind_native_frame {ε σ α β ρ : Type}
    (project : σ → ρ) (restore : ρ → σ → σ)
    (restoreSelf : ∀ state, restore (project state) state = state)
    (action : EStateM ε σ α) (original native : α → EStateM ε σ β)
    (initial : σ) (result : EStateM.Result ε σ α)
    (actionEq : action initial = result)
    (frame : SuccessFrame project initial result)
    (continuationEq : ∀ value state,
      original value (restore (project initial) state) = native value state) :
    EStateM.bind action original initial = resume native result := by
  rw [bind_resume action original initial result actionEq]
  cases result with
  | error error current => rfl
  | ok value current =>
    have same : project current = project initial := frame
    have restored : restore (project initial) current = current := by
      rw [← same]
      exact restoreSelf current
    change original value current = native value current
    exact (congrArg (original value) restored.symm).trans (continuationEq value current)

#print axioms intRange_loop_frame
#print axioms nativeIntRangeLoop_frame
#print axioms bind_native_frame
end StepRuntime

namespace StepRuntime
theorem successFrame_dite {ε σ α ρ : Type} (project : σ → ρ)
    (initial : σ) (condition : Prop) [Decidable condition]
    (yes : condition → EStateM.Result ε σ α)
    (no : ¬condition → EStateM.Result ε σ α)
    (hy : ∀ h, SuccessFrame project initial (yes h))
    (hn : ∀ h, SuccessFrame project initial (no h)) :
    SuccessFrame project initial (dite condition yes no) := by
  by_cases h : condition
  · simpa only [dite_eq_left h] using hy h
  · simpa only [dite_eq_right h] using hn h

theorem successFrame_ite {ε σ α ρ : Type} (project : σ → ρ)
    (initial : σ) (condition : Prop) [Decidable condition]
    (yes no : EStateM.Result ε σ α)
    (hy : condition → SuccessFrame project initial yes)
    (hn : ¬condition → SuccessFrame project initial no) :
    SuccessFrame project initial (ite condition yes no) := by
  by_cases h : condition
  · simpa only [ite_eq_left h] using hy h
  · simpa only [ite_eq_right h] using hn h

theorem projected_dite_eq {σ ρ : Type} (project : σ → ρ)
    (initial : σ) (condition : Prop) [Decidable condition]
    (yes : condition → σ) (no : ¬condition → σ)
    (hy : ∀ h, project (yes h) = project initial)
    (hn : ∀ h, project (no h) = project initial) :
    project (dite condition yes no) = project initial := by
  by_cases h : condition
  · simpa only [dite_eq_left h] using hy h
  · simpa only [dite_eq_right h] using hn h

theorem projected_ite_eq {σ ρ : Type} (project : σ → ρ)
    (initial : σ) (condition : Prop) [Decidable condition]
    (yes no : σ)
    (hy : condition → project yes = project initial)
    (hn : ¬condition → project no = project initial) :
    project (ite condition yes no) = project initial := by
  by_cases h : condition
  · simpa only [ite_eq_left h] using hy h
  · simpa only [ite_eq_right h] using hn h
end StepRuntime
namespace StepRuntime
theorem resume_successFrame {ε σ α β ρ : Type} (project : σ → ρ)
    (initial : σ) (continuation : α → EStateM ε σ β)
    (result : EStateM.Result ε σ α)
    (frame : SuccessFrame project initial result)
    (continuationFrame : ∀ value current,
      SuccessFrame project current (continuation value current)) :
    SuccessFrame project initial (resume continuation result) := by
  cases result with
  | error error current => trivial
  | ok value current =>
    exact successFrame_trans project initial current _ frame (continuationFrame value current)
end StepRuntime

namespace StepRuntime
theorem successFrame_pair {ε σ α ρ τ : Type}
    (first : σ → ρ) (second : σ → τ)
    (initial : σ) (result : EStateM.Result ε σ α)
    (firstFrame : SuccessFrame first initial result)
    (secondFrame : SuccessFrame second initial result) :
    SuccessFrame (fun state => (first state, second state)) initial result := by
  cases result with
  | error _ _ => trivial
  | ok _ _ => exact Prod.ext firstFrame secondFrame
#print axioms successFrame_pair
end StepRuntime

namespace StepRuntime
theorem resume_successFrame_fixed {ε σ α β ρ : Type} (project : σ → ρ)
    (initial : σ) (continuation : α → EStateM ε σ β)
    (result : EStateM.Result ε σ α)
    (frame : SuccessFrame project initial result)
    (continuationFrame : ∀ value current,
      SuccessFrame project initial (continuation value current)) :
    SuccessFrame project initial (resume continuation result) := by
  cases result with
  | error _ _ => trivial
  | ok value current => exact continuationFrame value current
#print axioms resume_successFrame_fixed
end StepRuntime

namespace StepRuntime
theorem resume_native_cont {ε σ α β : Type}
    (original native : α → EStateM ε σ β) (result : EStateM.Result ε σ α)
    (continuationEq : ∀ value current, original value current = native value current) :
    resume original result = resume native result := by
  cases result with
  | error _ _ => rfl
  | ok value current => exact continuationEq value current

theorem resume_native_frame {ε σ α β ρ : Type}
    (project : σ → ρ) (restore : ρ → σ → σ)
    (restoreSelf : ∀ state, restore (project state) state = state)
    (original native : α → EStateM ε σ β)
    (initial : σ) (result : EStateM.Result ε σ α)
    (frame : SuccessFrame project initial result)
    (continuationEq : ∀ value current,
      original value (restore (project initial) current) = native value current) :
    resume original result = resume native result := by
  cases result with
  | error _ _ => rfl
  | ok value current =>
    have same : project current = project initial := frame
    have restored : restore (project initial) current = current := by
      rw [← same]; exact restoreSelf current
    simpa [resume, restored] using continuationEq value current
#print axioms resume_native_cont
#print axioms resume_native_frame

theorem value_dite_eq {σ ρ : Type} (project : σ → ρ) (value : ρ)
    (condition : Prop) (inst : Decidable condition)
    (yes : condition → σ) (no : ¬condition → σ)
    (hy : ∀ h, project (yes h) = value) (hn : ∀ h, project (no h) = value) :
    project (@dite σ condition inst yes no) = value := by
  by_cases h : condition
  · simpa only [dite_eq_left h] using hy h
  · simpa only [dite_eq_right h] using hn h

theorem value_ite_eq {σ ρ : Type} (project : σ → ρ) (value : ρ)
    (condition : Prop) (inst : Decidable condition) (yes no : σ)
    (hy : condition → project yes = value) (hn : ¬condition → project no = value) :
    project (@ite σ condition inst yes no) = value := by
  by_cases h : condition
  · simpa only [ite_eq_left h] using hy h
  · simpa only [ite_eq_right h] using hn h

end StepRuntime
