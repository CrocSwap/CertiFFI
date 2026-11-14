-- ArmCert VALUE LAYER: run-level threading. `compileRun` folds `compile` over a plan;
-- `run_agrees` folds `step_agrees` over the actual run (any `run : Nat → St`, e.g. `stateAt real e`).
import ArmCertValue.StepAgrees
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
set_option autoImplicit false
namespace ArmCertValue
open HeapV2StepCerts.RegBind (Reg St regVal)

def compileRun (regions : List Region) : Sym → Nat → List StepV → Option (List Def × Sym)
  | σ, _, [] => some ([], σ)
  | σ, n, st :: rest => match compile σ n regions st with
    | some (ds, σ1) => match compileRun regions σ1 (n + ds.length) rest with
      | some (ds', σf) => some (ds ++ ds', σf)
      | none => none
    | none => none

theorem extend_append (vals : List (BitVec 64)) (ds ds' : List Def) :
    extend vals (ds ++ ds') = extend (extend vals ds) ds' := by
  simp [extend, List.foldl_append]

theorem extend_length (vals : List (BitVec 64)) : ∀ ds : List Def, (extend vals ds).length = vals.length + ds.length := by
  intro ds
  induction ds generalizing vals with
  | nil => simp [extend]
  | cons d t ih =>
    have : extend vals (d :: t) = extend (vals ++ [d.eval vals]) t := rfl
    rw [this, ih]
    simp [Nat.add_assoc, Nat.add_comm 1]

/-- The per-step value facts of a plan along a run, from index k. -/
def PlanHolds (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (regions : List Region)
    (run : Nat → St) (k : Nat) (plan : List StepV) : Prop :=
  ∀ j (h : j < plan.length), VHolds plan[j].us plan[j].fl (run (k + j)) (run (k + j + 1)) ∧
    MemVHolds mapping pinv regions plan[j].mem (run (k + j)) (run (k + j + 1))

theorem run_agrees (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (regions : List Region)
    (run : Nat → St) (hcoh : RegionCoherent mapping pinv) :
    ∀ (plan : List StepV) (k : Nat) (vals : List (BitVec 64)) (σ σf : Sym) (ds : List Def),
      Agrees mapping pinv vals σ (run k) → σ.Bounded vals.length →
      PlanHolds mapping pinv regions run k plan →
      compileRun regions σ vals.length plan = some (ds, σf) →
      Agrees mapping pinv (extend vals ds) σf (run (k + plan.length)) ∧
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
        obtain ⟨hA1, hB1⟩ := step_agrees hcoh hA hB h0.1 h0.2 h1
        have hlen : (extend vals ds1).length = vals.length + ds1.length := extend_length vals ds1
        have hp' : PlanHolds mapping pinv regions run (k + 1) rest := by
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

#print axioms run_agrees

end ArmCertValue
