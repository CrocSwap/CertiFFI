import Sail
namespace StepRuntime
theorem bitVec_length {n : Nat} (v : BitVec n) : Sail.BitVec.length v = n := rfl
theorem vector_length {α : Type u} {n : Nat} (v : Vector α n) : Sail.Vector.length v = n := rfl
variable {ε σ α β : Type}
theorem bind_ok (x : EStateM ε σ α) (k : α → EStateM ε σ β) (s : σ)
    (a : α) (s' : σ) (h : x s = .ok a s') : EStateM.bind x k s = k a s' := by
  simp only [EStateM.bind, h]
theorem bind_error (x : EStateM ε σ α) (k : α → EStateM ε σ β) (s : σ)
    (err : ε) (s' : σ) (h : x s = .error err s') : EStateM.bind x k s = .error err s' := by
  simp only [EStateM.bind, h]
theorem ok_congr {a a' : α} {s s' : σ} (ha : a = a') (hs : s = s') :
    (EStateM.Result.ok a s : EStateM.Result ε σ α) = .ok a' s' := by cases ha; cases hs; rfl
theorem error_congr {e e' : ε} {s s' : σ} (he : e = e') (hs : s = s') :
    (EStateM.Result.error e s : EStateM.Result ε σ α) = .error e' s' := by cases he; cases hs; rfl
theorem split_control {α : Sort u} (p : Prop) [Decidable p]
    (original : α) (yes : p → α) (no : ¬p → α)
    (hy : ∀ h, original = yes h) (hn : ∀ h, original = no h) :
    original = dite p yes no := by
  by_cases h : p
  · simpa only [dite_eq_left h] using hy h
  · simpa only [dite_eq_right h] using hn h
end StepRuntime

namespace StepRuntime
theorem split_ite {ι α : Type} (p : Prop) [Decidable p]
    (x y : ι → α) (s : ι) (a : p → α) (b : ¬p → α)
    (hx : ∀ h, x s = a h) (hy : ∀ h, y s = b h) :
    (if p then x else y) s = dite p a b := by
  by_cases h : p
  · simpa only [ite_eq_left h, dite_eq_left h] using hx h
  · simpa only [ite_eq_right h, dite_eq_right h] using hy h
theorem split_dite {ι α : Type} (p : Prop) [Decidable p]
    (x : p → ι → α) (y : ¬p → ι → α) (s : ι)
    (a : p → α) (b : ¬p → α)
    (hx : ∀ h, x h s = a h) (hy : ∀ h, y h s = b h) :
    (dite p x y) s = dite p a b := by
  by_cases h : p
  · simpa only [dite_eq_left h] using hx h
  · simpa only [dite_eq_right h] using hy h
theorem split_value_ite {α : Type} (p : Prop) [Decidable p]
    (x y : α) (a : p → α) (b : ¬p → α)
    (hx : ∀ h, x = a h) (hy : ∀ h, y = b h) :
    (if p then x else y) = dite p a b := by
  by_cases h : p
  · simpa only [ite_eq_left h, dite_eq_left h] using hx h
  · simpa only [ite_eq_right h, dite_eq_right h] using hy h
theorem split_value_dite {α : Type} (p : Prop) [Decidable p]
    (x : p → α) (y : ¬p → α) (a : p → α) (b : ¬p → α)
    (hx : ∀ h, x h = a h) (hy : ∀ h, y h = b h) :
    dite p x y = dite p a b := by
  by_cases h : p
  · simpa only [dite_eq_left h] using hx h
  · simpa only [dite_eq_right h] using hy h
def resume {ε σ α β : Type} (k : α → EStateM ε σ β) (r : EStateM.Result ε σ α) :
    EStateM.Result ε σ β := match r with
  | .ok a s => k a s
  | .error err s => .error err s
theorem bind_resume {ε σ α β : Type} (x : EStateM ε σ α) (k : α → EStateM ε σ β)
    (s : σ) (r : EStateM.Result ε σ α) (h : x s = r) :
    EStateM.bind x k s = resume k r := by cases r <;> simp only [EStateM.bind, h, resume]
theorem resume_ite {ε σ α β : Type} (k : α → EStateM ε σ β)
    (p : Prop) [Decidable p] (x y : EStateM.Result ε σ α) :
    resume k (if p then x else y) = if p then resume k x else resume k y := by
  split <;> rfl
theorem resume_dite {ε σ α β : Type} (k : α → EStateM ε σ β)
    (p : Prop) [Decidable p] (x : p → EStateM.Result ε σ α) (y : ¬p → EStateM.Result ε σ α) :
    resume k (dite p x y) = dite p (fun h => resume k (x h)) (fun h => resume k (y h)) := by
  split <;> rfl
theorem apply_ite {α β : Type} (f : α → β) (p : Prop) [Decidable p] (a b : α) :
    f (if p then a else b) = if p then f a else f b := by split <;> rfl
theorem apply_dite {α β : Type} (f : α → β) (p : Prop) [Decidable p]
    (a : p → α) (b : ¬p → α) :
    f (dite p a b) = dite p (fun h => f (a h)) (fun h => f (b h)) := by split <;> rfl
theorem merge_dite {α : Type} (p : Prop) [Decidable p] (a : α) :
    dite p (fun _ => a) (fun _ => a) = a := by split <;> rfl
theorem factor_ok_dite {ε σ α : Type} (p : Prop) [Decidable p]
    (a : p → α) (b : ¬p → α) (s : σ) :
    dite p (fun h => (EStateM.Result.ok (a h) s : EStateM.Result ε σ α))
      (fun h => EStateM.Result.ok (b h) s) = EStateM.Result.ok (dite p a b) s := by
  split <;> rfl
theorem factor_ok_states_dite {ε σ α : Type} (p : Prop) [Decidable p]
    (a : p → α) (b : ¬p → α) (s : p → σ) (t : ¬p → σ) :
    dite p (fun h => (EStateM.Result.ok (a h) (s h) : EStateM.Result ε σ α))
      (fun h => EStateM.Result.ok (b h) (t h)) =
      EStateM.Result.ok (dite p a b) (dite p s t) := by
  split <;> rfl
theorem bind_native_cont {ε σ α β : Type} (x : EStateM ε σ α)
    (k k' : α → EStateM ε σ β) (s : σ) (r : EStateM.Result ε σ α)
    (hx : x s = r) (h : ∀ a t, k a t = k' a t) :
    EStateM.bind x k s = resume k' r := by
  rw [bind_resume x k s r hx]
  cases r with
  | ok a t => exact h a t
  | error e t => rfl
end StepRuntime

namespace StepRuntime
/-- Transparent runtime control operator, with the original inclusive range,
early-done behavior, state and error propagation. Only the body is specialized. -/
def nativeIntRangeLoop {ε σ β : Type} (range : IntRange) (initial : β)
    (body : (i : Int) → i ∈ range → β → EStateM ε σ (ForInStep β))
    (state : σ) : EStateM.Result ε σ β :=
  IntRange.forIn' range initial body state

theorem intRangeLoop_congr {ε σ β : Type} (range : IntRange) (initial : β)
    (original native : (i : Int) → i ∈ range → β → EStateM ε σ (ForInStep β))
    (state : σ)
    (bodyEq : ∀ i membership value current,
      original i membership value current = native i membership value current) :
    IntRange.forIn' range initial original state =
      nativeIntRangeLoop range initial native state := by
  have same : original = native := by
    funext i membership value current
    exact bodyEq i membership value current
  rw [same]
  rfl
end StepRuntime

namespace StepRuntime
theorem resume_assoc {ε σ α β γ : Type}
    (k : β → EStateM ε σ γ) (j : α → EStateM ε σ β)
    (r : EStateM.Result ε σ α) :
    resume k (resume j r) = resume (fun a s => resume k (j a s)) r := by
  cases r <;> rfl
end StepRuntime
