-- H-P1 on the Sail run: the heap-v2 body's output region holds I^2 mod p, byte by byte.
-- Composes the generic value layer (run_agrees over the generated plan) with hp1_bytes.
-- Remaining inputs are hypotheses: the per-step value facts (PlanHolds: class tails +
-- Memory's memV_k) and the initial agreement at body entry.
import ArmCertValue.HeapV2Plan
import TranslateValue.HP1Square
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
set_option autoImplicit false
namespace ArmCertValue.HeapV2Plan
open ArmCertValue
open HeapV2StepCerts.RegBind (St)

theorem compiles_D : (compileRun regions σ0 68 plan).map (·.1) = some D := by decide +kernel

theorem outs_tracked : (compileRun regions σ0 68 plan).map (fun p => (List.range 32).map (p.2.memB O)) =
    some ((List.range 32).map fun j => some (outs.getD j (0, 0))) := by decide +kernel

theorem plan_length : plan.length = 357 := by decide +kernel

theorem σ0_bounded : σ0.Bounded 68 := by
  refine ⟨?_, ?_, ?_⟩
  · intro r i h
    cases r with
    | x k => simp only [σ0, Option.some.injEq] at h; omega
    | sp => simp only [σ0, Option.some.injEq] at h; omega
  · intro a b c d h
    simp only [σ0, Option.some.injEq, Prod.mk.injEq] at h
    omega
  · intro g j i k h
    simp only [σ0] at h
    split at h
    · next hc => simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · cases h

/-- **H-P1 on the run.** From body entry (run 0) to the body's end (run 357), given the per-step value
facts and the initial agreement, every output byte j < 32 of region O is byte j of I^2 mod p256k1, where
I is the little-endian value of the 32 input bytes (table inputs 0..31). -/
theorem hp1_run (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (run : Nat → St)
    (inputs : List (BitVec 64)) (hlen : inputs.length = 68) (hbytes : ∀ i, i < 32 → (inputs.getD i 0).toNat < 256)
    (hcoh : RegionCoherent mapping pinv)
    (hA0 : Agrees mapping pinv inputs σ0 (run 0))
    (hplan : PlanHolds mapping pinv regions run 0 plan) :
    ∀ j, j < 32 → regionByte mapping pinv (run 357) O j =
      some (BitVec.ofNat 8 ((TranslateValue.HP1.inVal inputs ^ 2 % TranslateValue.HP1.p256k1) / 256 ^ j)) := by
  obtain ⟨σf, hc⟩ : ∃ σf, compileRun regions σ0 68 plan = some (D, σf) := by
    have h := compiles_D
    cases hr : compileRun regions σ0 68 plan with
    | none => rw [hr] at h; cases h
    | some p =>
      obtain ⟨d, σf⟩ := p
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact ⟨σf, rfl⟩
  have hB0 : σ0.Bounded inputs.length := by rw [hlen]; exact σ0_bounded
  have hrun := run_agrees mapping pinv regions run hcoh plan 0 inputs σ0 σf D hA0 hB0 hplan (by rw [hlen]; exact hc)
  rw [plan_length, Nat.zero_add] at hrun
  have hout := outs_tracked
  rw [hc] at hout
  simp only [Option.map_some, Option.some.injEq] at hout
  intro j hj
  have hm : σf.memB O j = some (outs.getD j (0, 0)) := by
    have := congrArg (fun l => l[j]?) hout
    simpa [List.getElem?_map, List.getElem?_range hj] using this
  have hm' : σf.memB O j = some ((outs.getD j (0, 0)).1, (outs.getD j (0, 0)).2) := by
    rw [hm]
  rw [hrun.1.2.2 O j (outs.getD j (0, 0)).1 (outs.getD j (0, 0)).2 hm']
  exact congrArg some (TranslateValue.HP1.hp1_bytes inputs hlen hbytes j hj)

#print axioms hp1_run

end ArmCertValue.HeapV2Plan
