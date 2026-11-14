-- d199 pipeline: dispatch. Per-step routes (StepFact) and next obligations for every k < plan.length, plus
-- the invariant at entry, give the invariant along the whole run (chainG ∘ stepG). A program instance supplies the
-- two families by case split on k (generated per case by pipeline/gen_dispatch.py).
import ArmCertPipe.Deploy
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft
set_option autoImplicit false
namespace ArmCertPipe
open ArmCertValue CertiFFI.Prog.Generic.ModelRunView

/-- The `next` obligation of step k (the argument of `stepG`), as a named Prop. -/
abbrev NextOb (real : Type) [Sail.SailReal real] (Inv : Nat → NativeState → Prop) (mapping : BitVec 64 → Option Nat)
    (pinv : Nat → Nat) (regions : List Region) (σ0 : Sym) (inputs : List (BitVec 64)) (plan : List StepV) (k : Nat) :
    Prop :=
  ∀ x, Inv k x → (∀ fin, modelStep real x = .ok () fin → AgreesAt mapping pinv regions σ0 inputs plan (k + 1) fin) →
    ∃ fin, modelStep real x = .ok () fin ∧ Inv (k + 1) fin

/-- The whole run: the invariant at every step k < plan.length (chainG ∘ stepG up to the last step), and the last
    step's route alone gives the run's end with AgreesAt plan.length. The last step needs no `next` (its successor
    offset is not placed: a final RET / taken final branch leaves the plan). -/
theorem runG (real : Type) [Sail.SailReal real] {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {scope : Nat → Prop} {image : MemReloc.Image}
    {loadBase : MemReloc.Word} {base : BitVec 64} {offset : Nat → BitVec 64} {budget : Nat}
    {pinv : Nat → Nat} {regions : List Region} {σ0 : Sym} {inputs : List (BitVec 64)} {plan : List StepV}
    (entry : NativeState) (hne : 0 < plan.length)
    (init : InvG spec config rows mapping m scope image loadBase base offset budget pinv regions σ0 inputs plan 0 entry)
    (hcoh : RegionCoherent mapping pinv) (hall : (compileRun regions σ0 inputs.length plan).isSome = true)
    (route : ∀ k (hk : k < plan.length),
      StepFact real (InvG spec config rows mapping m scope image loadBase base offset budget pinv regions σ0 inputs plan)
        mapping pinv regions plan k hk)
    (next : ∀ k, k + 1 < plan.length →
      NextOb real (InvG spec config rows mapping m scope image loadBase base offset budget pinv regions σ0 inputs plan)
        mapping pinv regions σ0 inputs plan k) :
    (∀ k, k < plan.length →
      InvG spec config rows mapping m scope image loadBase base offset budget pinv regions σ0 inputs plan k
        (stateAt real entry k)) ∧
    ∃ fin, modelStep real (stateAt real entry (plan.length - 1)) = .ok () fin ∧
      AgreesAt mapping pinv regions σ0 inputs plan plan.length fin := by
  have chain := chainG real _ entry (plan.length - 1) init
    (fun k hk => stepG real hcoh hall k (by omega) (route k (by omega)) (next k (by omega)))
  refine ⟨fun k hk => chain k (by omega), ?_⟩
  have hj : plan.length - 1 < plan.length := by omega
  have inv := chain (plan.length - 1) (Nat.le_refl _)
  obtain ⟨fin, run, hv, hm⟩ := route (plan.length - 1) hj _ inv
  refine ⟨fin, run, ?_⟩
  have h := agreesAt_succ hcoh hj hall inv.extra hv hm
  rwa [Nat.sub_add_cancel hne] at h

#print axioms runG
end ArmCertPipe
