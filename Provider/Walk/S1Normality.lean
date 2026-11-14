import Walk.S1Unknowns
import Walk.S1KernelMemAttrsFrame
import Walk.S1LeafOutputPermsFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 300000
namespace S1Normality
abbrev State := SequentialState Regs oracleChoiceSource
def Frame (s t : State) : Prop := t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events
def Normal {α : Type} (p : SailM α) : Prop :=
  ∀ s, ∃ a t, p s = .ok a t ∧ Frame s t

theorem pure_normal {α : Type} (a : α) : Normal (pure a : SailM α) := by
  intro s
  exact ⟨a, s, rfl, rfl, rfl, rfl⟩
theorem assert_normal (b : Bool) (message : String) (h : b = true) :
    Normal (ArmFull.assert b message) := by
  subst b
  intro s
  exact ⟨(), s, rfl, rfl, rfl, rfl⟩
theorem bind_normal {α β : Type} (p : SailM α) (k : α → SailM β)
    (hp : Normal p) (hk : ∀ a, Normal (k a)) : Normal (p >>= k) := by
  intro s
  rcases hp s with ⟨a, t, ha, hr1, hm1, he1⟩
  rcases hk a t with ⟨b, u, hb, hr2, hm2, he2⟩
  refine ⟨b, u, ?_, hr2.trans hr1, hm2.trans hm1, he2.trans he1⟩
  simp [Bind.bind, EStateM.bind, ha, hb]
theorem map_normal {α β : Type} (f : α → β) (p : SailM α)
    (hp : Normal p) : Normal (f <$> p) := by
  intro s
  rcases hp s with ⟨a, t, ha, hf⟩
  refine ⟨f a, t, ?_, hf⟩
  simp [Functor.map, EStateM.map, ha]
theorem ite_normal {α : Type} (p : Prop) [Decidable p] (a b : SailM α)
    (ha : p → Normal a) (hb : ¬p → Normal b) : Normal (if p then a else b) := by
  by_cases h : p
  · simpa only [ite_eq_left h] using ha h
  · simpa only [ite_eq_right h] using hb h
theorem occ_normal (n : Nat) : Normal (occLabel n : SailM ChoiceLabel) := by
  intro s
  refine ⟨.occ n (s.choiceOcc.getD n 0),
    {s with choiceOcc := s.choiceOcc.insert n (s.choiceOcc.getD n 0 + 1)}, rfl,
    rfl, rfl, rfl⟩
theorem walk_normal (label : ChoiceLabel) : Normal (undefined_TTWState label ()) := by
  intro s
  exact S1Unknowns.undefined_walk_total label s
theorem address_normal (label : ChoiceLabel) : Normal (undefined_FullAddress label ()) := by
  intro s
  exact S1Unknowns.undefined_full_address_total label s
theorem bits_normal (n : Nat) (label : ChoiceLabel) : Normal (undefined_bitvector_at label n) := by
  intro s
  rcases S1Unknowns.bits_at_total n label s with ⟨d, h⟩
  exact ⟨d, s, h, rfl, rfl, rfl⟩
theorem attrs_normal (attr : BitVec 8) (sh : BitVec 2) (wp : S1TTWParams)
    (hValid : S1KernelMemAttrsFrame.Valid attr) : Normal (S1DecodeMemAttrs attr sh true wp) := by
  intro s
  exact S1KernelMemAttrsFrame.total attr sh wp s hValid
theorem permissions_normal (p : Permissions) (d : BitVec 64) (wp : S1TTWParams)
    (hD128 : wp.d128 = 0#1) : Normal (AArch64_S1ApplyOutputPerms p d .Regime_EL20 wp) := by
  intro s
  exact S1LeafOutputPermsFrame.total p d wp s hD128
#print axioms bind_normal
#print axioms map_normal
#print axioms ite_normal
#print axioms attrs_normal
end S1Normality
