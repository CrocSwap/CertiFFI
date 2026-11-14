-- ArmCert VALUE LAYER: run glue. Per-step value facts (the shape memory / emit as stepV_k)
-- plus an invariant along the actual run give PlanHolds on `stateAt real e`.
import ArmCertValue.Run
import CertiFFI.Prog.Generic.ModelRunView
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
set_option autoImplicit false
namespace ArmCertValue
open CertiFFI.Prog.Generic.ModelRunView
open ArmBridge.Boundary ArmBridge.Draft Uget.Chain

/-- The per-step fact every class tail / memory step emits (statement agreed with / memory /
): from any state satisfying the step-k invariant, the step succeeds and its value facts hold. -/
def StepFact (real : Type) [Sail.SailReal real] (Inv : Nat → NativeState → Prop)
    (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (regions : List Region) (plan : List StepV)
    (k : Nat) (h : k < plan.length) : Prop :=
  ∀ x, Inv k x → ∃ fin, modelStep real x = .ok () fin ∧
    VHolds plan[k].us plan[k].fl x fin ∧ MemVHolds mapping pinv regions plan[k].mem x fin

theorem stateAt_succ_of' {real : Type} [Sail.SailReal real] {s fin : NativeState} {k : Nat}
    (run : modelStep real (stateAt real s k) = .ok () fin) : stateAt real s (k + 1) = fin := by
  show next real (stateAt real s k) = fin
  unfold next; rw [run]

theorem planHolds_of_steps (real : Type) [Sail.SailReal real] (Inv : Nat → NativeState → Prop)
    (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (regions : List Region) (plan : List StepV)
    (e : NativeState)
    (hinv : ∀ k, k < plan.length → Inv k (stateAt real e k))
    (hstep : ∀ k (h : k < plan.length), StepFact real Inv mapping pinv regions plan k h) :
    PlanHolds mapping pinv regions (stateAt real e) 0 plan := by
  intro j hj
  obtain ⟨fin, run, hv, hm⟩ := hstep j hj _ (hinv j hj)
  have hs := stateAt_succ_of' run
  simp only [Nat.zero_add]
  rw [hs]
  exact ⟨hv, hm⟩

#print axioms planHolds_of_steps

end ArmCertValue
