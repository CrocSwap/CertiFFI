import Walk.S1CacheGuard
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 100000
namespace S1NormalME
open S1Normality

/- Normal return with a value predicate, preserving the state components needed
   to transport hardware configuration through the actual suffix. -/
def Ensures {R α : Type} (P : Regs → Prop) (p : SailME R α) (Q : α → Prop) : Prop :=
  ∀ s, P s.regs → ∃ a t, p s = .ok (.ok a) t ∧ Frame s t ∧ Q a

def Normal {R α : Type} (P : Regs → Prop) (p : SailME R α) : Prop :=
  Ensures P p (fun _ => True)

theorem pure_ensures {R α : Type} (P : Regs → Prop) (a : α) (Q : α → Prop)
    (h : Q a) : Ensures P (pure a : SailME R α) Q := by
  intro s _
  exact ⟨a, s, rfl, ⟨rfl, rfl, rfl⟩, h⟩

theorem bind_ensures {R α β : Type} (P : Regs → Prop)
    (p : SailME R α) (k : α → SailME R β) (Q : α → Prop) (U : β → Prop)
    (hp : Ensures P p Q) (hk : ∀ a, Q a → Ensures P (k a) U) :
    Ensures P (p >>= k) U := by
  intro s hs
  rcases hp s hs with ⟨a, t, ha, ⟨hr1, hm1, he1⟩, hq⟩
  have ht : P t.regs := by rw [hr1]; exact hs
  rcases hk a hq t ht with ⟨b, u, hb, ⟨hr2, hm2, he2⟩, hu⟩
  refine ⟨b, u, ?_, ⟨hr2.trans hr1, hm2.trans hm1, he2.trans he1⟩, hu⟩
  simp [Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, EStateM.bind, ha, hb]

theorem lift_normal {R α : Type} (P : Regs → Prop) (p : SailM α)
    (hp : S1Normality.Normal p) : Normal P (monadLift p : SailME R α) := by
  intro s _
  rcases hp s with ⟨a, t, ha, hf⟩
  refine ⟨a, t, ?_, hf, trivial⟩
  simp [monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.mk, Functor.map, EStateM.map, ha]

theorem ite_ensures {R α : Type} (P : Regs → Prop) (c : Prop) [Decidable c]
    (a b : SailME R α) (Q : α → Prop)
    (ha : c → Ensures P a Q) (hb : ¬c → Ensures P b Q) :
    Ensures P (if c then a else b) Q := by
  by_cases h : c
  · simpa only [ite_eq_left h] using ha h
  · simpa only [ite_eq_right h] using hb h

#print axioms bind_ensures
#print axioms lift_normal
end S1NormalME
namespace S1NormalME
open S1Normality

theorem normal_pure {R α : Type} (P : Regs → Prop) (a : α) :
    Normal P (pure a : SailME R α) := pure_ensures P a _ trivial

theorem normal_bind {R α β : Type} (P : Regs → Prop)
    (p : SailME R α) (k : α → SailME R β)
    (hp : Normal P p) (hk : ∀ a, Normal P (k a)) : Normal P (p >>= k) :=
  bind_ensures P p k _ _ hp (fun a _ => hk a)

theorem normal_ite {R α : Type} (P : Regs → Prop) (c : Prop) [Decidable c]
    (a b : SailME R α) (ha : c → Normal P a) (hb : ¬c → Normal P b) :
    Normal P (if c then a else b) := ite_ensures P c a b _ ha hb

theorem normal_map {R α β : Type} (P : Regs → Prop) (f : α → β)
    (p : SailME R α) (hp : Normal P p) : Normal P (f <$> p) := by
  intro s hs
  rcases hp s hs with ⟨a, t, ha, hf, _⟩
  refine ⟨f a, t, ?_, hf, trivial⟩
  simp [Functor.map, ExceptT.map, ExceptT.mk, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.map, ha]

theorem lift_conditional {R α : Type} (P : Regs → Prop) (p : SailM α)
    (hp : ∀ s, P s.regs → ∃ a t, p s = .ok a t ∧ Frame s t) :
    Normal P (monadLift p : SailME R α) := by
  intro s hs
  rcases hp s hs with ⟨a, t, ha, hf⟩
  refine ⟨a, t, ?_, hf, trivial⟩
  simp [monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.mk, Functor.map, EStateM.map, ha]

#print axioms normal_map
#print axioms lift_conditional
end S1NormalME
