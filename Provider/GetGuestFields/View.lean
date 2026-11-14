import GetGuestFields.Groups
import Walk.S1Normality
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace GetGuestFields
structure ActiveView where
  tgx : TGx
  d128 : BitVec 1
  aie : BitVec 1
  pnch : BitVec 1
  ds : BitVec 1
  mair : BitVec 64
  txsz : BitVec 6
  ps : BitVec 3

def active (wp : S1TTWParams) : ActiveView :=
  ⟨wp.tgx, wp.d128, wp.aie, wp.pnch, wp.ds, wp.mair, wp.txsz, wp.ps⟩

namespace Result
open S1Normality

def Returns {α : Type} (q : α → Prop) (p : SailM α) : Prop :=
  ∀ s, ∃ a t, p s = .ok a t ∧ Frame s t ∧ q a

theorem pure_returns {α : Type} (q : α → Prop) (a : α) (hq : q a) :
    Returns q (pure a : SailM α) := by
  intro s
  exact ⟨a, s, rfl, ⟨rfl, rfl, rfl⟩, hq⟩

theorem bind_returns {α β : Type} (q : β → Prop) (p : SailM α) (k : α → SailM β)
    (hp : Normal p) (hk : ∀ a, Returns q (k a)) : Returns q (p >>= k) := by
  intro s
  rcases hp s with ⟨a, t, hr, hf⟩
  rcases hk a t with ⟨b, u, hr2, hf2, hq⟩
  refine ⟨b, u, ?_, ⟨hf2.1.trans hf.1, hf2.2.1.trans hf.2.1, hf2.2.2.trans hf.2.2⟩, hq⟩
  simp [Bind.bind, EStateM.bind, hr, hr2]

theorem ite_returns {α : Type} (q : α → Prop) (p : Prop) [Decidable p]
    (a b : SailM α) (ha : p → Returns q a) (hb : ¬ p → Returns q b) :
    Returns q (if p then a else b) := by
  by_cases h : p
  · simpa only [ite_eq_left h] using ha h
  · simpa only [ite_eq_right h] using hb h
end Result
end GetGuestFields
