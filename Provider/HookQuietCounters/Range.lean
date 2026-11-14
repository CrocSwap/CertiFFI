import Sail.IntRange
import Lean.Elab.Command
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false

set_option autoImplicit false
set_option maxHeartbeats 100000


namespace HookQuietCounters

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Range.stepValue"
  (← IO.getStderr).flush

def stepValue {β : Type} : ForInStep β → β
  | .done b => b
  | .yield b => b

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Range.estate_bind_apply"
  (← IO.getStderr).flush

theorem estate_bind_apply {ε σ α β : Type} (x : EStateM ε σ α)
    (f : α → EStateM ε σ β) (s : σ) :
    (x >>= f) s = match x s with
      | .ok a t => f a t
      | .error e t => .error e t := rfl

/- A total-state invariant for the actual Sail integer-range iterator. -/
run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Range.range_loop"
  (← IO.getStderr).flush

theorem range_loop {ε σ β : Type} (range : IntRange)
    (f : (i : Int) → i ∈ range → β → EStateM ε σ (ForInStep β))
    (I : β → σ → Prop)
    (step : ∀ i hi b s, I b s → ∃ v t, f i hi b s = .ok v t ∧ I (stepValue v) t)
    (b : β) (i : Int) (hs : (i - range.start) % range.step = 0) (s : σ)
    (hI : I b s) :
    ∃ c t, IntRange.forIn'.loop range f b i hs s = .ok c t ∧ I c t := by
  rw [IntRange.forIn'.loop]
  split
  · rename_i hi
    obtain ⟨v, t, hv, ht⟩ := step i hi b s hI
    cases v with
    | done c =>
      exact ⟨c, t, by simp only [estate_bind_apply, hv]; rfl, ht⟩
    | yield c =>
      obtain ⟨d, u, hd, hu⟩ := range_loop range f I step c (i + range.step) (by
        rw [Int.add_comm, Int.add_sub_assoc]
        simpa using hs) t ht
      exact ⟨d, u, by simpa only [estate_bind_apply, hv] using hd, hu⟩
  · exact ⟨b, s, rfl, hI⟩
termination_by if range.step > 0 then (range.stop - i + 1).toNat else (i - range.stop + 1).toNat
decreasing_by
  have hne := range.step_pos
  have hr : (if range.step > 0 then range.start ≤ i ∧ i ≤ range.stop
      else range.stop ≤ i ∧ i ≤ range.start) ∧ (i - range.start) % range.step = 0 :=
    by assumption
  split
  · rw [IntRange.toNat_lt_toNat]
    · simp_all [Membership.mem]; omega
    · simp_all [Membership.mem]; omega
  · rw [IntRange.toNat_lt_toNat]
    · simp_all [Membership.mem]; omega
    · simp_all [Membership.mem]; omega

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Range.range_preserves"
  (← IO.getStderr).flush

theorem range_preserves {ε σ β : Type} (range : IntRange)
    (f : (i : Int) → i ∈ range → β → EStateM ε σ (ForInStep β))
    (I : β → σ → Prop)
    (step : ∀ i hi b s, I b s → ∃ v t, f i hi b s = .ok v t ∧ I (stepValue v) t)
    (b : β) (s : σ) (hI : I b s) :
    ∃ c t, IntRange.forIn' range b f s = .ok c t ∧ I c t := by
  exact range_loop range f I step b range.start (by simp) s hI

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Range.range_forIn_preserves"
  (← IO.getStderr).flush

theorem range_forIn_preserves {ε σ β : Type} (range : IntRange)
    (f : Int → β → EStateM ε σ (ForInStep β))
    (I : β → σ → Prop)
    (step : ∀ i, i ∈ range → ∀ b s,
      I b s → ∃ v t, f i b s = .ok v t ∧ I (stepValue v) t)
    (b : β) (s : σ) (hI : I b s) :
    ∃ c t, forIn range b f s = .ok c t ∧ I c t := by
  exact range_preserves range (fun i _ b => f i b) I step b s hI

#print axioms range_loop
#print axioms range_preserves
#print axioms range_forIn_preserves

end HookQuietCounters
