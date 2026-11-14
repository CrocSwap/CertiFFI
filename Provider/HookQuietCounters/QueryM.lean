import HookQuietCounters.PMUChoices
import HookQuietCounters.MonadLaws
import Lean.Elab.Command
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace HookQuietCounters

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.QueryM.QueryM"
  (← IO.getStderr).flush

def QueryM {α : Type} (x : SailM α) : Prop := ∀ s, QueryResult x s
namespace QueryM

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.QueryM.bind"
  (← IO.getStderr).flush

theorem bind {α β : Type} {x : SailM α} {f : α → SailM β}
    (hx : QueryM x) (hf : ∀ a, QueryM (f a)) : QueryM (x >>= f) := by
  intro s
  exact query_bind x f s (hx s) (fun a t _ => hf a t)

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.QueryM.ite"
  (← IO.getStderr).flush

theorem ite {α : Type} (p : Prop) [Decidable p] {x y : SailM α}
    (hx : QueryM x) (hy : QueryM y) : QueryM (if p then x else y) := by
  split <;> assumption

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.QueryM.pure"
  (← IO.getStderr).flush

theorem pure {α : Type} (a : α) : QueryM (Pure.pure a : SailM α) := query_pure a

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.QueryM.read"
  (← IO.getStderr).flush

theorem read {α : Type} (r : RegisterRef Regs α) : QueryM (readReg r : SailM α) := query_read r

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.QueryM.occ"
  (← IO.getStderr).flush

theorem occ (site : Nat) : QueryM (occLabel site : SailM ChoiceLabel) := by
  intro s
  exact ⟨_, afterOcc site s, rfl, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.QueryM.bool"
  (← IO.getStderr).flush

theorem bool (label : ChoiceLabel) : QueryM (undefined_bool_at label () : SailM Bool) := by
  intro s
  exact ⟨_, s, rfl, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.QueryM.bits"
  (← IO.getStderr).flush

theorem bits (label : ChoiceLabel) (n : Nat) : QueryM (undefined_bitvector_at label n : SailM (BitVec n)) := by
  intro s
  exact ⟨_, s, rfl, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.QueryM.int"
  (← IO.getStderr).flush

theorem int (label : ChoiceLabel) : QueryM (undefined_int_at label () : SailM Int) := by
  intro s
  exact ⟨_, s, rfl, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.QueryM.constraint"
  (← IO.getStderr).flush

theorem constraint (label : ChoiceLabel) : QueryM (undefined_Constraint label () : SailM Constraint) := by
  intro s
  obtain ⟨c, hc⟩ := undefined_constraint_total label s
  exact ⟨c, s, hc, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.QueryM.feature"
  (← IO.getStderr).flush

theorem feature (f : Feature) : QueryM (IsFeatureImplemented f : SailM Bool) := by
  intro s
  exact ⟨featureValue s f, s, feature_apply f s, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.QueryM.have_a64"
  (← IO.getStderr).flush

theorem have_a64 : QueryM (HaveAArch64 () : SailM Bool) := by
  intro s
  cases h0 : featureValue s .FEAT_AA64EL0 <;>
    cases h1 : featureValue s .FEAT_AA64EL1 <;>
    cases h2 : featureValue s .FEAT_AA64EL2 <;>
    cases h3 : featureValue s .FEAT_AA64EL3 <;>
    simp only [QueryResult, HaveAArch64, pure_apply, map_apply, feature_apply, h0, h1, h2, h3,
      Bool.or_false, Bool.or_true, Bool.false_or, Bool.true_or, Bool.false_eq_true, ite_true, ite_false, ↓reduceIte,
      Pure.pure, EStateM.pure, Bind.bind, EStateM.bind] <;>
    exact ⟨_, _, rfl, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.QueryM.assert"
  (← IO.getStderr).flush

theorem assert {b : Bool} (h : b = true) (msg : String) : QueryM (ArmFull.assert b msg : SailM Unit) := by
  intro s
  exact ⟨(), s, by rw [h]; rfl, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.QueryM.restc"
  (← IO.getStderr).flush

theorem restc : QueryM (ConstrainUnpredictableBits .Unpredictable_RESTC 2 : SailM (Constraint × (BitVec 2))) := by
  intro s
  obtain ⟨c, v, hc⟩ := constrain_restc_total s
  exact ⟨(c, v), _, hc, rfl⟩
end QueryM
#print axioms QueryM.bind
#print axioms QueryM.have_a64
#print axioms QueryM.restc
end HookQuietCounters
