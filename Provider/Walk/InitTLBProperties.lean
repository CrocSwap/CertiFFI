import Walk.InitBoolProbe
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace InitTLBProperties
abbrev State := SequentialState Regs oracleChoiceSource
def Keeps {α : Type} (p : SailM α) : Prop :=
  ∀ s, ∃ a t, p s = .ok a t ∧ t.regs.bank_Bool .__tlb_enabled = s.regs.bank_Bool .__tlb_enabled

theorem of_observation {α : Type} (p : SailM α)
    (h : ∀ s, InitBoolProbe.tlb (p s) = some (s.regs.bank_Bool .__tlb_enabled)) : Keeps p := by
  intro s
  have hf := h s
  cases hr : p s with
  | error e t => simp [hr, InitBoolProbe.tlb] at hf
  | ok a t =>
    simp only [hr, InitBoolProbe.tlb, Option.some.injEq] at hf
    exact ⟨a, t, rfl, hf⟩

theorem bind {α β : Type} {p : SailM α} {k : α → SailM β}
    (hp : Keeps p) (hk : ∀ a, Keeps (k a)) : Keeps (p >>= k) := by
  intro s
  rcases hp s with ⟨a, t, ha, ht⟩
  rcases hk a t with ⟨b, u, hb, hu⟩
  exact ⟨b, u, by simp [Bind.bind, EStateM.bind, ha, hb], hu.trans ht⟩

theorem observe_bind {α β : Type} (p : SailM α) (k : α → SailM β)
    (hk : ∀ a, Keeps (k a)) (s : State) :
    InitBoolProbe.tlb ((p >>= k) s) = InitBoolProbe.tlb (p s) := by
  cases hr : p s with
  | error err t => simp [Bind.bind, EStateM.bind, hr, InitBoolProbe.tlb]
  | ok a t =>
    rcases hk a t with ⟨b, u, hb, hu⟩
    simp [Bind.bind, EStateM.bind, hr, hb, InitBoolProbe.tlb, hu]
#print axioms bind
#print axioms observe_bind
end InitTLBProperties
