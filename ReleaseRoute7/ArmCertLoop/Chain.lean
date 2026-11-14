import Uget.Chain

open Sail Sail.ConcurrencyInterfaceV1
open ArmBridge.Boundary ArmBridge.Draft Uget.Chain

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

namespace ArmCertLoop.Aux

/-! Conditional proof combinators over the frozen Sail runner. These helpers
are not public release cards: consumers must derive all their progress facts
internally from actual instruction certificates and initial typed premises. -/

/-- Concatenate two successful segments of the actual Sail machine run. -/
theorem modelRun_append (real : Type) [Sail.SailReal real]
    (n m : Nat) (x y z : NativeState)
    (first : modelRun real n x = .ok () y)
    (second : modelRun real m y = .ok () z) :
    modelRun real (n + m) x = .ok () z := by
  induction n generalizing x with
  | zero =>
    have same : x = y := by simpa only [modelRun, EStateM.Result.ok.injEq, true_and] using first
    subst x
    simpa only [Nat.zero_add] using second
  | succ n ih =>
    cases step : modelStep real x with
    | error e bad => simp only [modelRun, step] at first; cases first
    | ok value mid =>
      have rest : modelRun real n mid = .ok () y := by
        simpa only [modelRun, step] using first
      simpa only [Nat.succ_add, modelRun, step] using ih mid rest

/-- A strict natural variant and bounded successful body/exit segments give a
successful finite Sail run and a derived bound. No state callbacks from this
helper may remain as public claim-card inputs. -/
theorem cutpoint_terminates (real : Type) [Sail.SailReal real]
    (H : Nat → Nat → NativeState → Prop)
    (E : Nat → NativeState → Prop)
    (bodyCost exitCost : Nat)
    (progress : ∀ rank elapsed x, H rank elapsed x →
      (∃ ticks y, ticks ≤ exitCost ∧
        modelRun real ticks x = .ok () y ∧ E (elapsed + ticks) y) ∨
      (∃ rank' ticks y, rank' < rank ∧ 0 < ticks ∧ ticks ≤ bodyCost ∧
        modelRun real ticks x = .ok () y ∧ H rank' (elapsed + ticks) y))
    (rank elapsed : Nat) (x : NativeState) (header : H rank elapsed x) :
    ∃ ticks y, ticks ≤ bodyCost * rank + exitCost ∧
      modelRun real ticks x = .ok () y ∧ E (elapsed + ticks) y := by
  induction rank using Nat.strongRecOn generalizing elapsed x with
  | ind rank ih =>
    rcases progress rank elapsed x header with exit | body
    · obtain ⟨ticks, y, cost, run, post⟩ := exit
      exact ⟨ticks, y, by omega, run, post⟩
    · obtain ⟨rank', ticks, y, lower, _positive, cost, run, next⟩ := body
      obtain ⟨rest, z, restCost, restRun, post⟩ := ih rank' lower (elapsed + ticks) y next
      refine ⟨ticks + rest, z, ?_, modelRun_append real ticks rest x y z run restRun, ?_⟩
      · calc
          ticks + rest ≤ bodyCost + (bodyCost * rank' + exitCost) := Nat.add_le_add cost restCost
          _ = bodyCost * (rank' + 1) + exitCost := by
            simp only [Nat.mul_add, Nat.mul_one]
            omega
          _ ≤ bodyCost * rank + exitCost :=
            Nat.add_le_add_right (Nat.mul_le_mul_left bodyCost (by omega)) exitCost
      · simpa only [Nat.add_assoc] using post

#print axioms modelRun_append
#print axioms cutpoint_terminates

end ArmCertLoop.Aux
