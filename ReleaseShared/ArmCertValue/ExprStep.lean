-- One composite arithmetic expression remains one machine instruction.
import ArmCertValue.ExprBatch
import ArmCertValue.F
import ArmCertValue.RegionAlias
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace ArmCertValue.G
open HeapV2StepCerts.RegBind (Reg St)
open ArmCertValue.Physical (BytePA)
open ArmCertValue.Expr

inductive Step where
  | legacy (step : F.Step)
  | reg (r : Reg) (term : Term)
  | flags (fn fz fc fv : Term)
  | regFlags (r : Reg) (term fn fz fc fv : Term)

/-- Normalize actual memory operands before compilation; arithmetic expressions
contain source register/flag/literal reads and have no region references. -/
def mapRegions (norm : Region → Region) : Step → Step
  | .legacy step => .legacy (RegionAlias.step norm step)
  | step => step

def planRegions (norm : Region → Region) (plan : List Step) : List Step := plan.map (mapRegions norm)

def outputs : Step → List (Location × Term)
  | .legacy _ => []
  | .reg r term => [(.reg r,term)]
  | .flags fn fz fc fv => [(.flag 0,fn),(.flag 1,fz),(.flag 2,fc),(.flag 3,fv)]
  | .regFlags r term fn fz fc fv =>
      [(.reg r,term),(.flag 0,fn),(.flag 1,fz),(.flag 2,fc),(.flag 3,fv)]

def Holds (bytePA : Physical.BytePA) (regions : List Region) : Step → St → St → Prop
  | .legacy step, x, y => F.Holds bytePA regions step x y
  | step, x, y => OutputHolds (outputs step) x y ∧ y.mem = x.mem

def compile (σ : Sym) (n : Nat) (regions : List Region) : Step → Option (List Def × Sym)
  | .legacy step => F.compile σ n regions step
  | .reg r term => (compileValue σ n term).map fun p => (p.1,writeRegMap σ r p.2)
  | .flags fn fz fc fv => do
      let (ds,ids) ← compileValues σ n [fn,fz,fc,fv]
      match ids with
      | [a,b,c,d] => pure (ds,writeFlagsMap σ a b c d)
      | _ => none
  | .regFlags r term fn fz fc fv => do
      let (ds,ids) ← compileValues σ n [term,fn,fz,fc,fv]
      match ids with
      | [id,a,b,c,d] => pure (ds,writeFlagsMap (writeRegMap σ r id) a b c d)
      | _ => none

theorem step_agrees {bytePA : Physical.BytePA} {vals : List (BitVec 64)} {σ τ : Sym}
    {x y : St} {regions : List Region} {step : Step} {ds : List Def}
    (agree : Physical.Agrees bytePA vals σ x) (bounded : σ.Bounded vals.length)
    (holds : Holds bytePA regions step x y)
    (compiled : compile σ vals.length regions step = some (ds,τ)) :
    Physical.Agrees bytePA (extend vals ds) τ y ∧ τ.Bounded (extend vals ds).length := by
  cases step with
  | legacy step => exact F.step_agrees agree bounded holds compiled
  | reg r term =>
    obtain ⟨p,hp,he⟩ := Option.map_eq_some_iff.1 compiled
    obtain ⟨more,id⟩ := p
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    have batch : compileValues σ vals.length [term] = some (more,[id]) := by
      simp [compileValues,hp]
    exact outputs_agree agree bounded [(.reg r,term)] more [id] batch
      (writeReg_bindings σ r term id) holds.1 holds.2
  | flags fn fz fc fv =>
    simp only [compile] at compiled
    cases h : compileValues σ vals.length [fn,fz,fc,fv] with
    | none => simp [h] at compiled
    | some p =>
      obtain ⟨more,ids⟩ := p
      simp [h] at compiled
      split at compiled
      · next a b c d =>
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj compiled)
        exact outputs_agree agree bounded (outputs (.flags fn fz fc fv)) more [a,b,c,d] h
          (writeFlags_bindings σ fn fz fc fv a b c d) holds.1 holds.2
      · cases compiled
  | regFlags r term fn fz fc fv =>
    simp only [compile] at compiled
    cases h : compileValues σ vals.length [term,fn,fz,fc,fv] with
    | none => simp [h] at compiled
    | some p =>
      obtain ⟨more,ids⟩ := p
      simp [h] at compiled
      split at compiled
      · next id a b c d =>
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj compiled)
        exact outputs_agree agree bounded (outputs (.regFlags r term fn fz fc fv)) more [id,a,b,c,d] h
          (writeRegFlags_bindings σ r term fn fz fc fv id a b c d) holds.1 holds.2
      · cases compiled

/-- Same per-step actual Sail success interface as the legacy pipeline, for the additive language. -/
def StepFact (real : Type) [Sail.SailReal real] (Inv : Nat → ArmBridge.Draft.NativeState → Prop)
    (bytePA : BytePA) (regions : List Region) (plan : List Step) (k : Nat) (hk : k < plan.length) : Prop :=
  ∀ x, Inv k x → ∃ fin, ArmBridge.Boundary.modelStep real x = .ok () fin ∧ Holds bytePA regions plan[k] x fin

def compileRun (regions : List Region) : Sym → Nat → List Step → Option (List Def × Sym)
  | σ, _, [] => some ([], σ)
  | σ, n, st :: rest => match compile σ n regions st with
    | some (ds, σ1) => match compileRun regions σ1 (n + ds.length) rest with
      | some (ds', σf) => some (ds ++ ds', σf)
      | none => none
    | none => none


def PlanHolds (bytePA : BytePA) (regions : List Region)
    (run : Nat → St) (k : Nat) (plan : List Step) : Prop :=
  ∀ j (h : j < plan.length), Holds bytePA regions plan[j] (run (k + j)) (run (k + j + 1))

theorem run_agrees (bytePA : BytePA) (regions : List Region)
    (run : Nat → St) :
    ∀ (plan : List Step) (k : Nat) (vals : List (BitVec 64)) (σ σf : Sym) (ds : List Def),
      Physical.Agrees bytePA vals σ (run k) → σ.Bounded vals.length →
      PlanHolds bytePA regions run k plan →
      compileRun regions σ vals.length plan = some (ds, σf) →
      Physical.Agrees bytePA (extend vals ds) σf (run (k + plan.length)) ∧
        σf.Bounded (extend vals ds).length := by
  intro plan
  induction plan with
  | nil =>
    intro k vals σ σf ds hA hB _ hc
    simp only [compileRun, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simpa [extend] using And.intro hA hB
  | cons st rest ih =>
    intro k vals σ σf ds hA hB hp hc
    simp only [compileRun] at hc
    split at hc
    · next ds1 σ1 h1 =>
      split at hc
      · next ds2 σ2 h2 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        have h0 := hp 0 (by simp)
        simp only [List.getElem_cons_zero, Nat.add_zero] at h0
        obtain ⟨hA1, hB1⟩ := step_agrees hA hB h0 h1
        have hlen : (extend vals ds1).length = vals.length + ds1.length := extend_length vals ds1
        have hp' : PlanHolds bytePA regions run (k + 1) rest := by
          intro j hj
          have := hp (j + 1) (by simp; omega)
          simp only [List.getElem_cons_succ] at this
          rw [show k + 1 + j = k + (j + 1) by omega]
          exact this
        have := ih (k + 1) (extend vals ds1) σ1 σ2 ds2 hA1 hB1 hp' (by rw [hlen]; exact h2)
        rw [extend_append, List.length_cons, show k + (rest.length + 1) = k + 1 + rest.length by omega]
        simpa using this
      · simp at hc
    · simp at hc



open CertiFFI.Prog.Generic.ModelRunView

theorem planHolds_of_steps (real : Type) [Sail.SailReal real]
    (Inv : Nat → ArmBridge.Draft.NativeState → Prop)
    (bytePA : BytePA) (regions : List Region) (plan : List Step)
    (e : ArmBridge.Draft.NativeState)
    (hinv : ∀ k, k < plan.length → Inv k (stateAt real e k))
    (hstep : ∀ k (h : k < plan.length), StepFact real Inv bytePA regions plan k h) :
    PlanHolds bytePA regions (stateAt real e) 0 plan := by
  intro j hj
  obtain ⟨fin, run, hh⟩ := hstep j hj _ (hinv j hj)
  have hs := Physical.stateAt_succ_of' run
  simp only [Nat.zero_add]
  rw [hs]
  exact hh

#print axioms run_agrees
#print axioms planHolds_of_steps

theorem compileRun_legacy (regions : List Region) :
    ∀ (plan : List F.Step) (σ : Sym) (n : Nat),
      compileRun regions σ n (plan.map Step.legacy) = F.compileRun regions σ n plan := by
  intro plan
  induction plan with
  | nil => intro σ n; rfl
  | cons step rest ih =>
    intro σ n
    simp only [List.map_cons,compileRun,F.compileRun,compile]
    cases F.compile σ n regions step with
    | none => rfl
    | some p =>
      obtain ⟨ds,τ⟩ := p
      simp only [ih]
      rfl

#print axioms compileRun_legacy
#print axioms step_agrees
end ArmCertValue.G
