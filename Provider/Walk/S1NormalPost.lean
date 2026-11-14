import Walk.S1Normality
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace S1NormalPost
open S1Normality

def Ensures {α : Type} (p : SailM α) (q : α → Prop) : Prop :=
  ∀ s, ∃ a t, p s = .ok a t ∧ Frame s t ∧ q a

theorem pure_post {α : Type} (a : α) (q : α → Prop) (ha : q a) :
    Ensures (pure a : SailM α) q := by
  intro s
  exact ⟨a, s, rfl, ⟨rfl, rfl, rfl⟩, ha⟩

theorem bind_post {α β : Type} (p : SailM α) (k : α → SailM β)
    (q : β → Prop) (hp : Normal p) (hk : ∀ a, Ensures (k a) q) :
    Ensures (p >>= k) q := by
  intro s
  rcases hp s with ⟨a, t, ha, hr1, hm1, he1⟩
  rcases hk a t with ⟨b, u, hb, ⟨hr2, hm2, he2⟩, hq⟩
  refine ⟨b, u, ?_, ⟨hr2.trans hr1, hm2.trans hm1, he2.trans he1⟩, hq⟩
  simp [Bind.bind, EStateM.bind, ha, hb]

theorem ite_post {α : Type} (p : Prop) [Decidable p] (a b : SailM α)
    (q : α → Prop) (ha : p → Ensures a q) (hb : ¬p → Ensures b q) :
    Ensures (if p then a else b) q := by
  by_cases h : p
  · simpa only [ite_eq_left h] using ha h
  · simpa only [ite_eq_right h] using hb h

theorem ite_pure {α : Type} (p : Prop) [Decidable p] (a b : α) :
    (if p then (pure a : SailM α) else pure b) = pure (if p then a else b) := by
  split <;> rfl
#print axioms bind_post
end S1NormalPost
