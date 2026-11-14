import Pilot.ExceptLoop
namespace StepRuntime

theorem intRange_loop_transport_frame {ε σ β ρ : Type}
    (project : σ → ρ) (restore : ρ → σ → σ)
    (restoreSelf : ∀ state, restore (project state) state = state)
    (range : IntRange)
    (original native : (i : Int) → i ∈ range → β → EStateM ε σ (ForInStep β))
    (initial : σ)
    (bodyEq : ∀ i member value current,
      original i member value (restore (project initial) current) = native i member value current)
    (bodyFrame : ∀ i member value current,
      SuccessFrame project initial (native i member value current))
    (value : β) (index : Int)
    (aligned : (index - range.start) % range.step = 0) :
    ∀ state, project state = project initial →
      IntRange.forIn'.loop range original value index aligned state =
        IntRange.forIn'.loop range native value index aligned state := by
  induction value, index, aligned using IntRange.forIn'.loop.induct range with
  | case1 value index aligned member ih =>
    intro state invariant
    have restored : restore (project initial) state = state := by
      rw [← invariant]; exact restoreSelf state
    have same := bodyEq index member value state
    rw [restored] at same
    conv => lhs; rw [IntRange.forIn'.loop.eq_1]
    conv => rhs; rw [IntRange.forIn'.loop.eq_1]
    simp only [dite_eq_left member]
    cases outcome : native index member value state with
    | error error current =>
      simp [Bind.bind, Pure.pure, EStateM.bind, same, outcome]
    | ok step current =>
      have frame := bodyFrame index member value state
      simp only [outcome, SuccessFrame] at frame
      cases step with
      | done value => simp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, same, outcome]
      | yield value =>
        simpa [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, same, outcome] using
          ih value current frame
  | case2 value index aligned outside =>
    intro state invariant
    conv => lhs; rw [IntRange.forIn'.loop.eq_1]
    conv => rhs; rw [IntRange.forIn'.loop.eq_1]
    simp [dite_eq_right outside]

theorem intRangeLoop_transport_frame {ε σ β ρ : Type}
    (project : σ → ρ) (restore : ρ → σ → σ)
    (restoreSelf : ∀ state, restore (project state) state = state)
    (range : IntRange) (value : β)
    (original native : (i : Int) → i ∈ range → β → EStateM ε σ (ForInStep β))
    (initial : σ)
    (bodyEq : ∀ i member value current,
      original i member value (restore (project initial) current) = native i member value current)
    (bodyFrame : ∀ i member value current,
      SuccessFrame project initial (native i member value current)) :
    IntRange.forIn' range value original initial = nativeIntRangeLoop range value native initial := by
  exact intRange_loop_transport_frame project restore restoreSelf range original native initial
    bodyEq bodyFrame value range.start (by simp) initial rfl

#print axioms intRange_loop_transport_frame
#print axioms intRangeLoop_transport_frame
end StepRuntime

namespace StepRuntime
theorem exceptIntRange_loop_transport_frame {δ ε σ β ρ : Type}
    (project : σ → ρ) (restore : ρ → σ → σ)
    (restoreSelf : ∀ state, restore (project state) state = state)
    (range : IntRange)
    (original native : (i : Int) → i ∈ range → β → ExceptT ε (EStateM δ σ) (ForInStep β))
    (initial : σ)
    (bodyEq : ∀ i member value current,
      original i member value (restore (project initial) current) = native i member value current)
    (bodyFrame : ∀ i member value current,
      SuccessFrame project initial (native i member value current))
    (value : β) (index : Int)
    (aligned : (index - range.start) % range.step = 0) :
    ∀ state, project state = project initial →
      IntRange.forIn'.loop range original value index aligned state =
        IntRange.forIn'.loop range native value index aligned state := by
  induction value, index, aligned using IntRange.forIn'.loop.induct range with
  | case1 value index aligned member ih =>
    intro state invariant
    have restored : restore (project initial) state = state := by
      rw [← invariant]; exact restoreSelf state
    have same := bodyEq index member value state
    rw [restored] at same
    conv => lhs; rw [IntRange.forIn'.loop.eq_1]
    conv => rhs; rw [IntRange.forIn'.loop.eq_1]
    simp only [dite_eq_left member]
    cases outcome : native index member value state with
    | error error current =>
      simp [Bind.bind, Pure.pure, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure, EStateM.bind, same, outcome]
    | ok result current =>
      have frame := bodyFrame index member value state
      simp only [outcome, SuccessFrame] at frame
      cases result with
      | error error =>
        simp [Bind.bind, Pure.pure, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
          ExceptT.pure, EStateM.bind, EStateM.pure, same, outcome]
      | ok step =>
        cases step with
        | done value =>
          simp [Bind.bind, Pure.pure, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
            ExceptT.pure, EStateM.bind, EStateM.pure, same, outcome]
        | yield value =>
          simpa [Bind.bind, Pure.pure, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
            ExceptT.pure, EStateM.bind, EStateM.pure, same, outcome] using
            ih value current frame
  | case2 value index aligned outside =>
    intro state invariant
    conv => lhs; rw [IntRange.forIn'.loop.eq_1]
    conv => rhs; rw [IntRange.forIn'.loop.eq_1]
    simp [dite_eq_right outside]

theorem exceptIntRangeLoop_transport_frame {δ ε σ β ρ : Type}
    (project : σ → ρ) (restore : ρ → σ → σ)
    (restoreSelf : ∀ state, restore (project state) state = state)
    (range : IntRange) (value : β)
    (original native : (i : Int) → i ∈ range → β → ExceptT ε (EStateM δ σ) (ForInStep β))
    (initial : σ)
    (bodyEq : ∀ i member value current,
      original i member value (restore (project initial) current) = native i member value current)
    (bodyFrame : ∀ i member value current,
      SuccessFrame project initial (native i member value current)) :
    IntRange.forIn' range value original initial = nativeExceptIntRangeLoop range value native initial := by
  exact exceptIntRange_loop_transport_frame project restore restoreSelf range original native initial
    bodyEq bodyFrame value range.start (by simp) initial rfl

#print axioms exceptIntRange_loop_transport_frame
#print axioms exceptIntRangeLoop_transport_frame
end StepRuntime

namespace StepRuntime
theorem intRange_loop_frame_fixed {ε σ β ρ : Type}
    (project : σ → ρ) (range : IntRange)
    (body : (index : Int) → index ∈ range → β → EStateM ε σ (ForInStep β))
    (initial : σ)
    (bodyFrame : ∀ index membership value state,
      SuccessFrame project initial (body index membership value state))
    (value : β) (index : Int)
    (aligned : (index - range.start) % range.step = 0) :
    ∀ state, project state = project initial → SuccessFrame project initial
      (IntRange.forIn'.loop range body value index aligned state) := by
  induction value, index, aligned using IntRange.forIn'.loop.induct range with
  | case1 value index aligned member ih =>
    intro state invariant
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
        have final := ih value current frame
        simpa [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, outcome] using final
  | case2 value index aligned outside =>
    intro state invariant
    rw [IntRange.forIn'.loop.eq_1]
    simpa [dite_eq_right outside, Pure.pure, EStateM.pure, SuccessFrame] using invariant

theorem exceptIntRange_loop_frame_fixed {δ ε σ β ρ : Type}
    (project : σ → ρ) (range : IntRange)
    (body : (i : Int) → i ∈ range → β → ExceptT ε (EStateM δ σ) (ForInStep β))
    (initial : σ)
    (bodyFrame : ∀ i membership value state,
      SuccessFrame project initial (body i membership value state))
    (value : β) (index : Int)
    (aligned : (index - range.start) % range.step = 0) :
    ∀ state, project state = project initial → SuccessFrame project initial
      (IntRange.forIn'.loop range body value index aligned state) := by
  induction value, index, aligned using IntRange.forIn'.loop.induct range with
  | case1 value index aligned member ih =>
    intro state invariant
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
          have final := ih value current frame
          simpa [Bind.bind, Pure.pure, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure, EStateM.bind,
            EStateM.pure, outcome] using final
  | case2 value index aligned outside =>
    intro state invariant
    rw [IntRange.forIn'.loop.eq_1]
    simpa [dite_eq_right outside, Pure.pure, ExceptT.mk, ExceptT.pure, EStateM.pure, SuccessFrame] using invariant


theorem nativeIntRangeLoop_frame_fixed {ε σ β ρ : Type}
    (project : σ → ρ) (range : IntRange) (value : β)
    (body : (i : Int) → i ∈ range → β → EStateM ε σ (ForInStep β))
    (initial state : σ)
    (bodyFrame : ∀ i member value current, SuccessFrame project initial (body i member value current))
    (invariant : project state = project initial) :
    SuccessFrame project initial (nativeIntRangeLoop range value body state) := by
  exact intRange_loop_frame_fixed project range body initial bodyFrame value range.start (by simp) state invariant

theorem nativeExceptIntRangeLoop_frame_fixed {δ ε σ β ρ : Type}
    (project : σ → ρ) (range : IntRange) (value : β)
    (body : (i : Int) → i ∈ range → β → ExceptT ε (EStateM δ σ) (ForInStep β))
    (initial state : σ)
    (bodyFrame : ∀ i member value current, SuccessFrame project initial (body i member value current))
    (invariant : project state = project initial) :
    SuccessFrame project initial (nativeExceptIntRangeLoop range value body state) := by
  exact exceptIntRange_loop_frame_fixed project range body initial bodyFrame value range.start (by simp) state invariant
#print axioms nativeIntRangeLoop_frame_fixed
#print axioms nativeExceptIntRangeLoop_frame_fixed

end StepRuntime
