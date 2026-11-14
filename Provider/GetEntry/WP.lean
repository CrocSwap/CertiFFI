import Walk.S1NormalME
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 100000
namespace S1EntryWP
abbrev State := S1Normality.State

def Post {R α : Type} (next : α → State → Prop) (exit : R → State → Prop)
    (result : Except (Sail.Error exception ⊕ R) α) (t : State) : Prop :=
  match result with
  | .ok a => next a t
  | .error (.inr r) => exit r t
  | .error (.inl _) => False

def WP {R α : Type} (p : SailME R α) (s : State)
    (next : α → State → Prop) (exit : R → State → Prop) : Prop :=
  ∃ result t, p s = .ok result t ∧ Post next exit result t

theorem pure_wp {R α : Type} (a : α) (s : State)
    (next : α → State → Prop) (exit : R → State → Prop) (h : next a s) :
    WP (pure a : SailME R α) s next exit := ⟨.ok a, s, rfl, h⟩

theorem lift_wp {R α : Type} (p : SailM α) (s t : State) (a : α)
    (next : α → State → Prop) (exit : R → State → Prop)
    (hr : p s = .ok a t) (h : next a t) :
    WP (monadLift p : SailME R α) s next exit := by
  refine ⟨.ok a, t, ?_, h⟩
  simp [monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.mk, Functor.map, EStateM.map, hr]

theorem bind_wp {R α β : Type} (p : SailME R α) (k : α → SailME R β)
    (s : State) (next : β → State → Prop) (exit : R → State → Prop)
    (hp : WP p s (fun a t => WP (k a) t next exit) exit) :
    WP (p >>= k) s next exit := by
  rcases hp with ⟨result, t, hr, hpost⟩
  cases result with
  | ok a =>
    rcases hpost with ⟨result, u, hk, hu⟩
    refine ⟨result, u, ?_, hu⟩
    simp [Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, EStateM.bind, Pure.pure, EStateM.pure, hr, hk]
  | error e =>
    refine ⟨.error e, t, ?_, ?_⟩
    · simp [Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, EStateM.bind, Pure.pure, EStateM.pure, hr]
    · cases e <;> exact hpost

theorem run_wp {R : Type} (p : SailME R R) (s : State) (post : R → State → Prop)
    (hp : WP p s post post) :
    ∃ r t, SailME.run p s = .ok r t ∧ post r t := by
  rcases hp with ⟨result, t, hr, hpost⟩
  cases result with
  | ok r =>
    refine ⟨r, t, ?_, hpost⟩
    simp [SailME.run, Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run,
      ExceptT.run, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, hr]
  | error e =>
    cases e with
    | inl err => exact False.elim hpost
    | inr r =>
      refine ⟨r, t, ?_, hpost⟩
      simp [SailME.run, Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run,
        ExceptT.run, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, hr]
#print axioms bind_wp
#print axioms run_wp

theorem of_run {R : Type} (p : SailME R R) (s t : State) (r : R)
    (post : R → State → Prop) (hrun : SailME.run p s = .ok r t) (hp : post r t) :
    WP p s post post := by
  cases h : p s with
  | error e u =>
    simp [SailME.run, Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run,
      ExceptT.run, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, h] at hrun
  | ok result u =>
    cases result with
    | ok a =>
      have heq : EStateM.Result.ok a u =
          (EStateM.Result.ok r t : EStateM.Result (Sail.Error exception) State R) := by
        simpa [SailME.run, Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run,
          ExceptT.run, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, h] using hrun
      have hparts := EStateM.Result.ok.inj heq
      rcases hparts with ⟨rfl, rfl⟩
      exact ⟨.ok a, u, h, hp⟩
    | error e =>
      cases e with
      | inl err =>
        simp [SailME.run, Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run,
          ExceptT.run, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, h] at hrun
        change EStateM.Result.error err u = EStateM.Result.ok r t at hrun
        cases hrun
      | inr a =>
        have heq : EStateM.Result.ok a u =
            (EStateM.Result.ok r t : EStateM.Result (Sail.Error exception) State R) := by
          simpa [SailME.run, Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run,
            ExceptT.run, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, h] using hrun
        have hparts := EStateM.Result.ok.inj heq
        rcases hparts with ⟨rfl, rfl⟩
        exact ⟨.error (.inr a), u, h, hp⟩
#print axioms of_run


theorem bind_lift_eq {R α β : Type} (p : SailM α) (k : α → SailME R β)
    (s t : State) (a : α) (next : β → State → Prop) (exit : R → State → Prop)
    (hp : p s = .ok a t) (hk : WP (k a) t next exit) :
    WP ((monadLift p : SailME R α) >>= k) s next exit := by
  apply bind_wp
  exact lift_wp p s t a _ exit hp hk

theorem bind_lift_normal {R α β : Type} (p : SailM α) (k : α → SailME R β)
    (s : State) (next : β → State → Prop) (exit : R → State → Prop)
    (hp : S1Normality.Normal p)
    (hk : ∀ a t, S1Normality.Frame s t → WP (k a) t next exit) :
    WP ((monadLift p : SailME R α) >>= k) s next exit := by
  rcases hp s with ⟨a, t, hr, hf⟩
  exact bind_lift_eq p k s t a next exit hr (hk a t hf)

theorem map_wp {R α β : Type} (f : α → β) (p : SailME R α) (s : State)
    (next : β → State → Prop) (exit : R → State → Prop)
    (hp : WP p s (fun a t => next (f a) t) exit) : WP (f <$> p) s next exit := by
  rcases hp with ⟨result, t, hr, hpost⟩
  cases result with
  | ok a =>
    refine ⟨.ok (f a), t, ?_, hpost⟩
    simp [Functor.map, ExceptT.map, ExceptT.mk, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, hr]
  | error e =>
    refine ⟨.error e, t, ?_, ?_⟩
    · simp [Functor.map, ExceptT.map, ExceptT.mk, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, hr]
    · cases e <;> exact hpost

theorem frame_trans {s t u : State} (hst : S1Normality.Frame s t) (htu : S1Normality.Frame t u) :
    S1Normality.Frame s u := ⟨htu.1.trans hst.1, htu.2.1.trans hst.2.1, htu.2.2.trans hst.2.2⟩
#print axioms bind_lift_normal
#print axioms map_wp


theorem bind_normal_me {R α β : Type} (p : SailME R α) (k : α → SailME R β)
    (s : State) (next : β → State → Prop) (exit : R → State → Prop)
    (hp : S1NormalME.Normal (fun _ => True) p)
    (hk : ∀ a t, S1Normality.Frame s t → WP (k a) t next exit) :
    WP (p >>= k) s next exit := by
  rcases hp s trivial with ⟨a, t, hr, hf, _⟩
  apply bind_wp
  exact ⟨.ok a, t, hr, hk a t hf⟩
#print axioms bind_normal_me

end S1EntryWP
