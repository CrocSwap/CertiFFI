import Uget.Chain
import Lean.Elab.Command
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register

namespace CertiFFI.Prog.Generic.ModelRunView
open ArmBridge.Boundary ArmBridge.Draft Uget.Chain

/-! The state at each prefix of a successful native path. Error successors are
defined so `stateAt` is total; the invariant theorem below proves that the
observed prefixes actually take successful model steps. -/

run_cmd do
  IO.eprintln "CURRENT_DECL CertiFFI.Prog.Generic.ModelRunView.next"
  (← IO.getStderr).flush

def next (real : Type) [Sail.SailReal real] (s : NativeState) : NativeState :=
  match modelStep real s with
  | .ok _ t => t
  | .error _ t => t

run_cmd do
  IO.eprintln "CURRENT_DECL CertiFFI.Prog.Generic.ModelRunView.stateAt"
  (← IO.getStderr).flush

def stateAt (real : Type) [Sail.SailReal real] (s : NativeState) : Nat → NativeState
  | 0 => s
  | k + 1 => next real (stateAt real s k)

run_cmd do
  IO.eprintln "CURRENT_DECL CertiFFI.Prog.Generic.ModelRunView.stateAt_succ_start"
  (← IO.getStderr).flush

theorem stateAt_succ_start (real : Type) [Sail.SailReal real] (s : NativeState) (n : Nat) :
    stateAt real s (n + 1) = stateAt real (next real s) n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (next real) ih

run_cmd do
  IO.eprintln "CURRENT_DECL ModelRunView.stateAt_of_run"
  (← IO.getStderr).flush

/- A total prefix selector agrees with the actual final state only after success. -/
run_cmd do
  IO.eprintln "CURRENT_DECL CertiFFI.Prog.Generic.ModelRunView.stateAt_of_run"
  (← IO.getStderr).flush

theorem stateAt_of_run (real : Type) [Sail.SailReal real] (n : Nat)
    (s fin : NativeState) (h : modelRun real n s = .ok () fin) : stateAt real s n = fin := by
  induction n generalizing s with
  | zero => cases h; rfl
  | succ n ih =>
    cases step : modelStep real s with
    | error e bad => simp only [modelRun, step] at h; cases h
    | ok value mid =>
      have rest : modelRun real n mid = .ok () fin := by simpa only [modelRun, step] using h
      simpa only [stateAt_succ_start, next, step] using ih mid rest

run_cmd do
  IO.eprintln "CURRENT_DECL ModelRunView.steps_of_run"
  (← IO.getStderr).flush

/- Success of the partial runner proves success at every computed prefix. -/
run_cmd do
  IO.eprintln "CURRENT_DECL CertiFFI.Prog.Generic.ModelRunView.steps_of_run"
  (← IO.getStderr).flush

theorem steps_of_run (real : Type) [Sail.SailReal real] (n : Nat)
    (s fin : NativeState) (h : modelRun real n s = .ok () fin) :
    ∀ k, k < n → modelStep real (stateAt real s k) = .ok () (stateAt real s (k + 1)) := by
  induction n generalizing s with
  | zero => intro k hk; omega
  | succ n ih =>
    cases step : modelStep real s with
    | error e bad => simp only [modelRun, step] at h; cases h
    | ok value mid =>
      have rest : modelRun real n mid = .ok () fin := by simpa only [modelRun, step] using h
      intro k hk
      cases k with
      | zero => simpa only [stateAt, next, step] using step
      | succ k => simpa only [stateAt_succ_start, next, step] using ih mid rest k (by omega)

run_cmd do
  IO.eprintln "CURRENT_DECL ModelRunView.segment_of_run"
  (← IO.getStderr).flush

/- Every bounded segment of a successful partial run succeeds on its actual prefix states. -/
run_cmd do
  IO.eprintln "CURRENT_DECL CertiFFI.Prog.Generic.ModelRunView.segment_of_run"
  (← IO.getStderr).flush

theorem segment_of_run (real : Type) [Sail.SailReal real] (total : Nat)
    (s fin : NativeState) (h : modelRun real total s = .ok () fin)
    (n start : Nat) (bound : start + n ≤ total) :
    modelRun real n (stateAt real s start) = .ok () (stateAt real s (start + n)) := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    have step := steps_of_run real total s fin h start (by omega)
    rw [modelRun, step]
    have rest := ih (start + 1) (by omega)
    have index : (start + 1) + n = start + (n + 1) := by omega
    simpa only [index] using rest

run_cmd do
  IO.eprintln "CURRENT_DECL ModelRunView.invariant_prefixes"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL CertiFFI.Prog.Generic.ModelRunView.invariant_prefixes"
  (← IO.getStderr).flush

theorem invariant_prefixes (real : Type) [Sail.SailReal real]
    (Inv : Nat → NativeState → Prop) (n : Nat)
    (hstep : ∀ k, k < n → Step real (Inv k) (Inv (k + 1)))
    (s : NativeState) (h0 : Inv 0 s) :
    ∀ k, k ≤ n → Inv k (stateAt real s k) := by
  intro k
  induction k with
  | zero => intro _; exact h0
  | succ k ih =>
    intro hk
    obtain ⟨t, ht, hi⟩ := hstep k (by omega) _ (ih (by omega))
    simpa only [stateAt, next, ht] using hi

run_cmd do
  IO.eprintln "CURRENT_DECL ModelRunView.steps_successful"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL CertiFFI.Prog.Generic.ModelRunView.steps_successful"
  (← IO.getStderr).flush

theorem steps_successful (real : Type) [Sail.SailReal real]
    (Inv : Nat → NativeState → Prop) (n : Nat)
    (hstep : ∀ k, k < n → Step real (Inv k) (Inv (k + 1)))
    (s : NativeState) (h0 : Inv 0 s) :
    ∀ k, k < n → modelStep real (stateAt real s k) = .ok () (stateAt real s (k + 1)) := by
  intro k hk
  obtain ⟨t, ht, _⟩ := hstep k hk _
    (invariant_prefixes real Inv n hstep s h0 k (by omega))
  simpa only [stateAt, next, ht] using ht

#print axioms invariant_prefixes
#print axioms steps_successful
#print axioms stateAt_of_run
#print axioms steps_of_run
#print axioms segment_of_run
end CertiFFI.Prog.Generic.ModelRunView
