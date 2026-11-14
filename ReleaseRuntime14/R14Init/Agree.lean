-- Memory (d200 P2(B)). The value-layer entry agreement at step 0 from region bytes in memory: for any state whose
-- input-region bytes are all present (decided per case against the entry plan), AgreesAt … 0 holds with
-- inputs = certiffi's mkInputsL over the bytes read off the state. Generic; the per-case checks are SYNTHETIC.
import ArmCertValue.ReleaseGen
import ArmCertPipe.Prefix
import NativeSourceInit.PhysicalPlan
set_option autoImplicit false
namespace R14Init
open ArmCertValue

/-- Inverse of memBL: the (region, byte) at table position i. -/
def posL : List (Region × Nat) → Nat → Nat → Option (Region × Nat)
  | [], _, _ => none
  | (R, nb) :: t, base, i => if base ≤ i ∧ i < base + nb then some (R, i - base) else posL t (base + nb) i

theorem posL_of_memBL : ∀ (rs : List (Region × Nat)) (base : Nat) (g : Region) (j i k : Nat),
    memBL rs base g j = some (i, k) → posL rs base i = some (g, j) := by
  intro rs
  induction rs with
  | nil => intro base g j i k h; simp [memBL] at h
  | cons p t ih =>
    obtain ⟨R, nb⟩ := p
    intro base g j i k h
    simp only [memBL] at h
    split at h
    · next hc =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, hj⟩ := hc
      simp only [posL]
      rw [if_pos (show _ from by omega)]
      congr 2; omega
    · have hb := (memBL_spec t (base + nb) g j i k h).2.1
      simp only [posL]
      rw [if_neg (by omega)]
      exact ih (base + nb) g j i k h

/-- The input bytes read off a state. -/
def bytesOf (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (x : ArmBridge.Draft.NativeState) (rs : List (Region × Nat)) (i : Nat) :
    BitVec 8 :=
  match posL rs 0 i with
  | some (g, j) => (regionByte mapping pinv x g j).getD 0
  | none => 0

theorem memBL_mem : ∀ (rs : List (Region × Nat)) (base : Nat) (g : Region) (j i k : Nat),
    memBL rs base g j = some (i, k) → ∃ nb, (g, nb) ∈ rs ∧ j < nb := by
  intro rs
  induction rs with
  | nil => intro base g j i k h; simp [memBL] at h
  | cons p t ih =>
    obtain ⟨R, nb⟩ := p
    intro base g j i k h
    simp only [memBL] at h
    split at h
    · next hc => obtain ⟨rfl, hj⟩ := hc; exact ⟨nb, List.mem_cons_self .., hj⟩
    · obtain ⟨n, m, hj⟩ := ih (base + nb) g j i k h; exact ⟨n, List.mem_cons_of_mem _ m, hj⟩

/-- Decidable presence check of every input-region byte in the plan. -/
def presentOK (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (plan : NativeSourceInit.Plan)
    (rs : List (Region × Nat)) : Bool :=
  rs.all fun r => (List.range r.2).all fun j =>
    match mapping (BitVec.ofInt 64 ((pinv r.1.pin : Int) + r.1.off + j)) with
    | some pa => plan.any (·.1 == pa)
    | none => false

theorem agreesAt_zero_of_plan (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (regions : List Region)
    (rs : List (Region × Nat)) (plan : List StepV) (memPlan : NativeSourceInit.Plan) (x : ArmBridge.Draft.NativeState)
    (hm : NativeSourceInit.Satisfies memPlan x.mem) (ok : presentOK mapping pinv memPlan rs = true) :
    ArmCertPipe.AgreesAt mapping pinv regions (σ0L rs) (mkInputsL x rs (bytesOf mapping pinv x rs)) plan 0 x := by
  refine ArmCertPipe.agreesAt_zero (agrees_σ0L mapping pinv x rs _ ?_) ?_
  · intro g j i k h
    have hp := posL_of_memBL rs 0 g j i k h
    obtain ⟨nb, m, hj⟩ := memBL_mem rs 0 g j i k h
    have c := List.all_eq_true.1 (List.all_eq_true.1 ok (g, nb) m) j (List.mem_range.2 hj)
    simp only [bytesOf, hp]
    unfold regionByte
    revert c
    cases hpa : mapping (BitVec.ofInt 64 ((pinv g.pin : Int) + g.off + j)) with
    | none => intro c; simp at c
    | some pa =>
      intro c
      obtain ⟨row, rm, re⟩ := List.any_eq_true.1 c
      have e : row.1 = pa := beq_iff_eq.1 re
      have hv := hm row rm
      rw [e] at hv
      simp [hv]
  · simp only [mkInputsL, mkInputsG_length]; exact σ0L_bounded rs

#print axioms agreesAt_zero_of_plan
end R14Init
