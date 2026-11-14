import Spike91.View
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace Uget.Chain
open ArmBridge.Boundary ArmBridge.Draft ArmCert.Premises.TranslationAgreesV1 ArmBridge.CruxCore Spike91

/-! a design decision stage 3, invariant-only chain: per-step invariants carry explicit register/memory facts,
    so no view composition is needed. No LNSym. -/

def modelRun (real : Type) [Sail.SailReal real] : Nat → NativeState → EStateM.Result (Sail.Error exception) NativeState Unit
  | 0, s => .ok () s
  | n + 1, s => match (modelStep real) s with
    | .ok _ t => modelRun real n t
    | .error e t => .error e t

theorem modelRun_succ (real : Type) [Sail.SailReal real] (n : Nat) (s t : NativeState)
    (h : (modelStep real) s = .ok () t) : modelRun real (n + 1) s = modelRun real n t := by
  simp only [modelRun, h]

def Step (real : Type) [Sail.SailReal real] (P Q : NativeState → Prop) : Prop :=
  ∀ s, P s → ∃ fin, (modelStep real) s = .ok () fin ∧ Q fin

theorem chain (real : Type) [Sail.SailReal real] (Inv : Nat → NativeState → Prop) (n : Nat)
    (h : ∀ k, k < n → Step real (Inv k) (Inv (k + 1))) :
    ∀ s, Inv 0 s → ∃ fin, modelRun real n s = .ok () fin ∧ Inv n fin := by
  suffices H : ∀ r j s, j + r = n → Inv j s → ∃ fin, modelRun real r s = .ok () fin ∧ Inv n fin by
    intro s hs; exact H n 0 s (by omega) hs
  intro r
  induction r with
  | zero => intro j s hj hs; have : j = n := by omega
            subst this; exact ⟨s, rfl, hs⟩
  | succ r ih =>
    intro j s hj hs
    obtain ⟨t, ht, hInv⟩ := h j (by omega) s hs
    obtain ⟨fin, h1, h2⟩ := ih (j + 1) t (by omega) hInv
    exact ⟨fin, by rw [modelRun_succ real r s t ht]; exact h1, h2⟩

/-- Adapter for the summary shape AFTER FinExport export lands (the view equation is then
    unconditional). No hypothesis quantifies FinExport over an arbitrary witness T (that would be
    unsatisfiable); until the export lands the generated summaries keep (FinExport fin (R T) → …). -/
theorem ofSummary (real : Type) [Sail.SailReal real] (m : ConsumerMap) (P Q : NativeState → Prop)
    (U : View → View) (R : NativeState → NativeState)
    (hsum : ∀ s, P s → ∃ fin T, (modelStep real) s = .ok () fin ∧ ArmBridge.BoundaryV2.UnmappedSame m s fin ∧
      StepPins fin ∧ SysEq2 s.regs fin.regs ∧ T.mem = s.mem ∧ fin.mem = (R T).mem ∧ view m fin = U (view m s))
    (hnext : ∀ s fin T, P s → ArmBridge.BoundaryV2.UnmappedSame m s fin → StepPins fin → SysEq2 s.regs fin.regs →
      T.mem = s.mem → fin.mem = (R T).mem → view m fin = U (view m s) → Q fin) :
    Step real P Q := by
  intro s hs
  obtain ⟨fin, T, hms, hU, hp, hsy, hTm, hfm, hv⟩ := hsum s hs
  exact ⟨fin, hms, hnext s fin T hs hU hp hsy hTm hfm hv⟩

#print axioms chain
#print axioms ofSummary
end Uget.Chain
