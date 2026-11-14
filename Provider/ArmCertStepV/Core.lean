-- Memory: generic pieces of stepV_k.
--  (a) MemVHolds [] (the 251 non-memory steps): memV_nil_of_bytes / memV_nil_of_mem / memV_nil_of_written.
--  (b) VHolds from RegBind.Holds + the NZCV frame, under a decidable per-register compatibility check Compat.
import HeapV2StepCerts.RegBindCore
import HeapV2StepCerts.Flags
import ArmCertValue.Core
import ArmCertValueMem.Region
set_option autoImplicit false
namespace ArmCertValue.StepVCore
open ArmCertValue ArmCertValue.MemRegion
open HeapV2StepCerts.RegBind (Reg St regVal Upd updOf Holds)

/-! ## (a) MemVHolds with no memory effects -/

/-- MemVHolds [] from: every tracked region byte reads the same before and after. -/
theorem memV_nil_of_bytes (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (regions : List Region) (x y : St)
    (h : ∀ r ∈ regions, ∀ j, j < 8 * r.words → regionByte mapping pinv y r j = regionByte mapping pinv x r j) :
    MemVHolds mapping pinv regions [] x y := by
  refine ⟨fun e he => absurd he (List.not_mem_nil), ?_, ?_⟩
  · intro r hr w hw _ _ _
    exact regionWord_congr mapping pinv x y r w (fun k hk => h r hr (8 * w + k) (by omega))
  · intro r hr j hj _ _ _
    exact h r hr j hj

/-- MemVHolds [] from an unchanged memory (class / branch / BL / RET steps: R gives fin.mem = x.mem). -/
theorem memV_nil_of_mem (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (regions : List Region) (x y : St)
    (h : y.mem = x.mem) : MemVHolds mapping pinv regions [] x y :=
  memV_nil_of_bytes mapping pinv regions x y (fun r _ j _ => by simp only [regionByte, h])

/-- MemVHolds [] from a write set (e.g. fetch AF/DBM table writes) that misses every tracked region byte's PA. -/
theorem memV_nil_of_written (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (regions : List Region) (x y : St)
    (written : Nat → Prop) (wo : ∀ pa, ¬ written pa → y.mem[pa]? = x.mem[pa]?)
    (miss : ∀ r ∈ regions, ∀ j, j < 8 * r.words → ∀ pa,
      mapping (BitVec.ofInt 64 ((pinv r.pin : Int) + r.off + j)) = some pa → ¬ written pa) :
    MemVHolds mapping pinv regions [] x y := by
  refine memV_nil_of_bytes mapping pinv regions x y (fun r hr j hj => ?_)
  simp only [regionByte]
  cases hm : mapping (BitVec.ofInt 64 ((pinv r.pin : Int) + r.off + j)) with
  | none => rfl
  | some pa => exact wo pa (miss r hr j hj pa hm)

/-! ## (b) VHolds from RegBind.Holds -/

/-- One register: the plan entry (none = unlisted, some none = clobbered, some (some u)) against RegBind's Upd. -/
def okUpd : Option (Option VUpd) → Upd → Bool
  | none, .keep => true
  | some none, _ => true
  | some (some u), .set s c => u == ⟨.add, [.reg s, .lit (BitVec.ofInt 64 c)]⟩
  | _, _ => false

/-- The plan's register list agrees with RegBind's on every register (decidable). -/
def Compat (vus : List (Reg × Option VUpd)) (rus : List (Reg × Upd)) : Prop :=
  (∀ i : Fin 31, okUpd ((vus.find? (·.1 = .x i)).map (·.2)) (updOf rus (.x i)) = true) ∧
    okUpd ((vus.find? (·.1 = .sp)).map (·.2)) (updOf rus .sp) = true

instance (vus : List (Reg × Option VUpd)) (rus : List (Reg × Upd)) : Decidable (Compat vus rus) := by
  unfold Compat; infer_instance

theorem vholds_of_holds {vus : List (Reg × Option VUpd)} {fl : Option (VUpd × VUpd × VUpd × VUpd)}
    {rus : List (Reg × Upd)} {x y : St}
    (c : Compat vus rus) (hfl : fl = none) (h : Holds rus x y)
    (nz : HeapV2StepCerts.Flags.nzcv y.regs = HeapV2StepCerts.Flags.nzcv x.regs) :
    VHolds vus fl x y := by
  subst hfl
  refine ⟨fun r => ?_, ?_⟩
  · have cr : okUpd ((vus.find? (·.1 = r)).map (·.2)) (updOf rus r) = true := by
      cases r with
      | x i => exact c.1 i
      | sp => exact c.2
    have hr := h r
    revert cr hr
    generalize (vus.find? (·.1 = r)).map (·.2) = v
    generalize updOf rus r = u
    intro cr hr
    rcases v with _ | _ | w
    · cases u <;> simp_all [okUpd]
    · trivial
    · cases u with
      | keep => simp [okUpd] at cr
      | drop => simp [okUpd] at cr
      | set s k =>
        have e : w = ⟨.add, [.reg s, .lit (BitVec.ofInt 64 k)]⟩ := by
          simp only [okUpd] at cr; exact beq_iff_eq.1 cr
        subst e
        simp only at hr ⊢
        rw [hr]; rfl
  · simp only [HeapV2StepCerts.Flags.nzcv, Prod.mk.injEq] at nz
    obtain ⟨hn, hz, hc, hv⟩ := nz
    intro i
    match i with
    | 0 => simp only [flagWord, hn]
    | 1 => simp only [flagWord, hz]
    | 2 => simp only [flagWord, hc]
    | 3 => simp only [flagWord, hv]

#print axioms memV_nil_of_mem
#print axioms memV_nil_of_written
#print axioms vholds_of_holds
end ArmCertValue.StepVCore
