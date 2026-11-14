import ArmCertCTOrdered.OrderedEventV2
import Bridge.CruxGenGuarded.EntryTraffic
import Bridge.CruxGenGuarded.EntryClassNext
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Draft
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

-- d193 split (certiffi): Sail-side content only; the LNSym content moved to Bridge.CruxGenGuarded.PhasedCTLNSym.
namespace ArmBridge.CruxGenGuarded.PhasedCT

/-! phased-CT typing CORE. Two paired actual runs `L k`, `R k` (reached states
of the left/right executions) and a per-step typing relation `Rel k` (the phase's
public-operand agreement: public relation + scaffold dispositions). If every
step preserves `Rel` and, under `Rel`, produces record-equal appended event deltas
and equal successor PCs (per-class `TimingEq` at rec:= V2 record),
then the WHOLE run's appended traces are record-equal and the final PCs agree.
Nothing about secrets, payloads or the step semantics is assumed here; those enter
only through the per-step obligation. -/

/-- Timing-relevant agreement of a paired segment, over a record projection. -/
def TimingRec {α : Type} (rec : Event → α) (l r tl tr : NativeState) : Prop :=
  (∃ dl dr : Array Event, tl.events = l.events ++ dl ∧ tr.events = r.events ++ dr ∧
    dl.toList.map rec = dr.toList.map rec) ∧ tl.regs._PC = tr.regs._PC

theorem timing_trans {α : Type} (rec : Event → α) (l r ml mr tl tr : NativeState)
    (h1 : TimingRec rec l r ml mr) (h2 : TimingRec rec ml mr tl tr) : TimingRec rec l r tl tr := by
  obtain ⟨⟨d1, e1, hl1, hr1, he1⟩, _⟩ := h1
  obtain ⟨⟨d2, e2, hl2, hr2, he2⟩, pc⟩ := h2
  refine ⟨⟨d1 ++ d2, e1 ++ e2, ?_, ?_, ?_⟩, pc⟩
  · rw [hl2, hl1, Array.append_assoc]
  · rw [hr2, hr1, Array.append_assoc]
  · simp only [Array.toList_append, List.map_append, he1, he2]

theorem timing_refl {α : Type} (rec : Event → α) (l r : NativeState) (pc : l.regs._PC = r.regs._PC) :
    TimingRec rec l r l r :=
  ⟨⟨#[], #[], by simp, by simp, rfl⟩, pc⟩

run_cmd do
  IO.eprintln "CURRENT_DECL PhasedCT.phased"
  (← IO.getStderr).flush

/-- The typing core: per-step preservation + per-step timing ⇒ whole-run timing. -/
theorem phased {α : Type} (rec : Event → α) (L R : Nat → NativeState)
    (Rel : Nat → NativeState → NativeState → Prop) (n : Nat)
    (init : Rel 0 (L 0) (R 0)) (pc0 : (L 0).regs._PC = (R 0).regs._PC)
    (step : ∀ k, k < n → Rel k (L k) (R k) →
      TimingRec rec (L k) (R k) (L (k + 1)) (R (k + 1)) ∧ Rel (k + 1) (L (k + 1)) (R (k + 1))) :
    TimingRec rec (L 0) (R 0) (L n) (R n) ∧ Rel n (L n) (R n) := by
  induction n with
  | zero => exact ⟨timing_refl rec _ _ pc0, init⟩
  | succ n ih =>
    obtain ⟨t, rel⟩ := ih (fun k hk => step k (Nat.lt_succ_of_lt hk))
    obtain ⟨t', rel'⟩ := step n (Nat.lt_succ_self n) rel
    exact ⟨timing_trans rec _ _ _ _ _ _ t t', rel'⟩

/-- Instantiated at the frozen ordered V2 records: paired runs have equal
ordered record traces over the whole run. -/
theorem phased_records (L R : Nat → NativeState)
    (Rel : Nat → NativeState → NativeState → Prop) (n : Nat)
    (init : Rel 0 (L 0) (R 0)) (pc0 : (L 0).regs._PC = (R 0).regs._PC)
    (step : ∀ k, k < n → Rel k (L k) (R k) →
      TimingRec ArmCertCTOrdered.OrderedEventV2.record (L k) (R k) (L (k + 1)) (R (k + 1)) ∧
        Rel (k + 1) (L (k + 1)) (R (k + 1))) :
    TimingRec ArmCertCTOrdered.OrderedEventV2.record (L 0) (R 0) (L n) (R n) :=
  (phased _ L R Rel n init pc0 step).1

end ArmBridge.CruxGenGuarded.PhasedCT

