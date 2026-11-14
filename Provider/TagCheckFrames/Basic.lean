import NativeMteTagCheck.Transport
import Lean
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace TagCheckFrames
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
end TagCheckFrames
