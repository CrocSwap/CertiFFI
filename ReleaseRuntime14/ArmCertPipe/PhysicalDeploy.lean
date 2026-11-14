-- d199 pipeline: the program-generic deployment premises and E17 chain. A program instance supplies its
-- consumer map / code scope / image / offsets (P1, P2), and per step k a route (StepFact over ChainInvG with the
-- AgreesAt extra) plus a nextG lemma (RtG / Memory ArmCertMemPipe). stepG glues the two: the route's
-- VHolds + MemVHolds discharge the nextG lemma's `extra (k+1)` obligation through agreesAt_succ and determinism.
import ArmCertPipe.ChainInvG
import ArmCertPipe.Prefix
import ArmCertValue.PhysicalGlue
import ArmCertPipe.PhysicalPrefix
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft
set_option autoImplicit false
namespace ArmCertPipe.Physical
open ArmCertValue CertiFFI.Prog.Generic.ModelRunView
open ArmCertValue.Physical (BytePA StepFact)

/-- The chain invariant of a program: ChainInvG with the value-layer extra. -/
abbrev InvG {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word) (base : BitVec 64)
    (offset : Nat → BitVec 64) (budget : Nat) (bytePA : BytePA) (regions : List Region) (σ0 : Sym)
    (inputs : List (BitVec 64)) (plan : List StepV) (k : Nat) (x : NativeState) : Prop :=
  ChainInvG spec config rows mapping m scope image loadBase base offset budget
    (AgreesAt bytePA regions σ0 inputs plan) k x

/-- DEPLOYMENT premises of a program instance (the generic analogue of E17General.DeploymentPremises). -/
structure DeploymentPremisesG {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word) (base : BitVec 64)
    (offset : Nat → BitVec 64) (budget : Nat) (bytePA : BytePA) (regions : List Region) (σ0 : Sym)
    (inputs : List (BitVec 64)) (plan : List StepV) (entry : NativeState) : Prop where
  separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte
  page : base.toNat % 4096 = 0
  low : base.toNat < 2 ^ 54
  agrees : ConsumerMapAgrees spec mapping m
  room : plan.length ≤ budget
  /-- The chain invariant at body entry (incl. the entry agreement, e.g. certiffi's agrees_σ0L). -/
  init : InvG spec config rows mapping m scope image loadBase base offset budget bytePA regions σ0 inputs plan 0 entry

/-- One chain step: a route (the step's value facts) and a nextG lemma give ChainInvG with the AgreesAt extra at k+1. -/
theorem stepG (real : Type) [Sail.SailReal real] {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {scope : Nat → Prop} {image : MemReloc.Image}
    {loadBase : MemReloc.Word} {base : BitVec 64} {offset : Nat → BitVec 64} {budget : Nat}
    {bytePA : BytePA} {regions : List Region} {σ0 : Sym} {inputs : List (BitVec 64)} {plan : List StepV}
    (hall : (compileRun regions σ0 inputs.length plan).isSome = true)
    (k : Nat) (hk : k < plan.length)
    (route : StepFact real (InvG spec config rows mapping m scope image loadBase base offset budget bytePA regions σ0 inputs plan)
      bytePA regions plan k hk)
    (next : ∀ x, InvG spec config rows mapping m scope image loadBase base offset budget bytePA regions σ0 inputs plan k x →
      (∀ fin, modelStep real x = .ok () fin → AgreesAt bytePA regions σ0 inputs plan (k + 1) fin) →
      ∃ fin, modelStep real x = .ok () fin ∧
        InvG spec config rows mapping m scope image loadBase base offset budget bytePA regions σ0 inputs plan (k + 1) fin) :
    ∀ x, InvG spec config rows mapping m scope image loadBase base offset budget bytePA regions σ0 inputs plan k x →
      ∃ fin, modelStep real x = .ok () fin ∧
        InvG spec config rows mapping m scope image loadBase base offset budget bytePA regions σ0 inputs plan (k + 1) fin := by
  intro x inv
  apply next x inv
  intro fin run
  obtain ⟨fin', run', hv, hm⟩ := route x inv
  have e : fin' = fin := by
    rw [run] at run'; cases run'; rfl
  subst e
  exact agreesAt_succ hk hall inv.extra hv hm

/-- **The program's E17 chain**: from the deployment premises and per-step preservation, the invariant holds at every
    state of the run up to the plan's end. -/
theorem chainG (real : Type) [Sail.SailReal real] (Inv : Nat → NativeState → Prop) (e : NativeState) (n : Nat)
    (init : Inv 0 e)
    (step : ∀ k, k < n → ∀ x, Inv k x → ∃ fin, modelStep real x = .ok () fin ∧ Inv (k + 1) fin) :
    ∀ k, k ≤ n → Inv k (stateAt real e k) := by
  intro k
  induction k with
  | zero => intro _; exact init
  | succ j ih =>
    intro hj
    obtain ⟨fin, run, hinv⟩ := step j (by omega) _ (ih (by omega))
    rw [ArmCertValue.Physical.stateAt_succ_of' run]; exact hinv

#print axioms stepG
#print axioms chainG
end ArmCertPipe.Physical
