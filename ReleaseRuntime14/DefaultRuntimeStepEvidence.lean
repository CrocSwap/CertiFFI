-- One actual successor gives the physical, vector, and event conclusions.
import DefaultRuntimeMemory
import ArmCertPipe.EvFrame

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxGenGuarded
open CertiFFI.Prog.Generic.ModelRunView

set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ReleaseProfile.DefaultRuntime

abbrev StepEvidence (real : Type) [Sail.SailReal real] {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (mapping : BitVec 64 → Option Nat)
    (Inv : Nat → NativeState → Prop) (records : List (Option ArmCertCTOrdered.OrderedEventV2.Record))
    (k : Nat) : Prop :=
  ∀ x, Inv k x → ∃ fin, modelStep real x = .ok () fin ∧ Inv (k + 1) fin ∧
    fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧
    StepEvents.EvShape spec mapping records x fin

theorem StepEvidence.evOb {real : Type} [Sail.SailReal real] {domain : QueryDomain}
    {spec : TopologyImageSpec domain} {mapping : BitVec 64 → Option Nat}
    {Inv : Nat → NativeState → Prop} {records : List (Option ArmCertCTOrdered.OrderedEventV2.Record)}
    {k : Nat} (step : StepEvidence real spec mapping Inv records k) :
    ArmCertPipe.EvOb real spec mapping Inv records k := by
  apply ArmCertPipe.evob_of_route
  intro x inv
  obtain ⟨fin, run, _, _, _, ev⟩ := step x inv
  exact ⟨fin, run, ev⟩

theorem StepEvidence.frame {real : Type} [Sail.SailReal real] {domain : QueryDomain}
    {spec : TopologyImageSpec domain} {mapping : BitVec 64 → Option Nat}
    {Inv : Nat → NativeState → Prop} {records : List (Option ArmCertCTOrdered.OrderedEventV2.Record)}
    {k : Nat} (step : StepEvidence real spec mapping Inv records k) :
    ∀ x fin, Inv k x → modelStep real x = .ok () fin → fin.regs._Z = x.regs._Z := by
  intro x fin inv run
  obtain ⟨fin', run', _, z, _, _⟩ := step x inv
  rw [run] at run'
  cases run'
  exact z

theorem StepEvidence.advance {real : Type} [Sail.SailReal real] {domain : QueryDomain}
    {spec : TopologyImageSpec domain} {mapping : BitVec 64 → Option Nat}
    {Inv : Nat → NativeState → Prop} {records : List (Option ArmCertCTOrdered.OrderedEventV2.Record)}
    {k : Nat} (step : StepEvidence real spec mapping Inv records k) :
    ∀ x, Inv k x → ∃ fin, modelStep real x = .ok () fin ∧ Inv (k + 1) fin := by
  intro x inv
  obtain ⟨fin, run, next, _, _, _⟩ := step x inv
  exact ⟨fin, run, next⟩

theorem chain_of_evidence (real : Type) [Sail.SailReal real] {domain : QueryDomain}
    {spec : TopologyImageSpec domain} {mapping : BitVec 64 → Option Nat}
    {Inv : Nat → NativeState → Prop}
    (entry : NativeState) (n : Nat) (init : Inv 0 entry)
    (records : Nat → List (Option ArmCertCTOrdered.OrderedEventV2.Record))
    (steps : ∀ k, k < n → StepEvidence real spec mapping Inv (records k) k) :
    (∀ k, k ≤ n → Inv k (stateAt real entry k)) ∧
    (∀ k, k ≤ n → (stateAt real entry k).regs._Z = entry.regs._Z) := by
  have inv := ArmCertPipe.Physical.chainG real Inv entry n init
    (fun k hk => (steps k hk).advance)
  refine ⟨inv, ?_⟩
  intro k
  induction k with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    obtain ⟨fin, run, _, z, _, _⟩ := steps j (by omega) _ (inv j (by omega))
    rw [ArmCertValue.Physical.stateAt_succ_of' run]
    exact z.trans (ih (by omega))

/-- T6b: one step keeps PSTATE.DIT (determinism of modelStep). -/
theorem StepEvidence.dit {real : Type} [Sail.SailReal real] {domain : QueryDomain}
    {spec : TopologyImageSpec domain} {mapping : BitVec 64 → Option Nat}
    {Inv : Nat → NativeState → Prop} {records : List (Option ArmCertCTOrdered.OrderedEventV2.Record)}
    {k : Nat} (step : StepEvidence real spec mapping Inv records k) :
    ∀ x fin, Inv k x → modelStep real x = .ok () fin → fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT := by
  intro x fin inv run
  obtain ⟨fin', run', _, _, d, _⟩ := step x inv
  rw [run] at run'
  cases run'
  exact d

/-- **T6b DIT frame along the evidence chain**: every state 0..n has the entry's PSTATE.DIT. -/
theorem dit_of_evidence (real : Type) [Sail.SailReal real] {domain : QueryDomain}
    {spec : TopologyImageSpec domain} {mapping : BitVec 64 → Option Nat}
    {Inv : Nat → NativeState → Prop}
    (entry : NativeState) (n : Nat) (init : Inv 0 entry)
    (records : Nat → List (Option ArmCertCTOrdered.OrderedEventV2.Record))
    (steps : ∀ k, k < n → StepEvidence real spec mapping Inv (records k) k) :
    ∀ k, k ≤ n → (stateAt real entry k).regs.PSTATE.DIT = entry.regs.PSTATE.DIT := by
  have inv := (chain_of_evidence real entry n init records steps).1
  intro k
  induction k with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    obtain ⟨fin, run, _, _, d, _⟩ := steps j (by omega) _ (inv j (by omega))
    rw [ArmCertValue.Physical.stateAt_succ_of' run]
    exact d.trans (ih (by omega))

#print axioms StepEvidence.evOb
#print axioms StepEvidence.frame
#print axioms chain_of_evidence
#print axioms StepEvidence.dit
#print axioms dit_of_evidence
end ReleaseProfile.DefaultRuntime
