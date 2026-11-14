import TagCheckFrames.Basic
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace TagCheckFrames
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
end TagCheckFrames
