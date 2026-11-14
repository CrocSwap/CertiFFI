-- Canonical entry SSA inputs read from the actual fixed caller state.
import ArmCertValue.PhysicalRelease
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCertValue.Physical.Entry
open HeapV2StepCerts.RegBind (St)

def snapshot (view : BytePA) (s : St) : List (Region × Nat) → Nat → BitVec 8
  | [], _ => 0
  | (r,n) :: rest, i => if i < n then (regionByte view s r i).getD 0
    else snapshot view s rest (i-n)

/-- The symbolic memory table and the physical snapshot use the same first
region occurrence and concatenation offsets, including zero-width regions. -/
theorem snapshot_memBL (view : BytePA) (s : St) :
    ∀ (rs : List (Region × Nat)) (base : Nat) (g : Region) (j i k : Nat),
      memBL rs base g j = some (i,k) →
      snapshot view s rs (i-base) = (regionByte view s g j).getD 0 := by
  intro rs
  induction rs with
  | nil => intro base g j i k h; simp [memBL] at h
  | cons p rest ih =>
    obtain ⟨r,n⟩ := p
    intro base g j i k h
    simp only [memBL] at h
    split at h
    · next hit =>
      obtain ⟨rfl,bound⟩ := hit
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      simp only [snapshot, Nat.add_sub_cancel_left, if_pos bound]
    · have bounds := memBL_spec rest (base+n) g j i k h
      have ge : n ≤ i-base := by omega
      rw [snapshot,if_neg (by omega)]
      have index : i-base-n = i-(base+n) := by omega
      rw [index]
      exact ih (base+n) g j i k h

/-- Byte presence is required only in this entry state. The snapshot definition
then supplies every tracked input without a per-program memory identity proof. -/
theorem snapshot_agrees (view : BytePA) (s : St) (rs : List (Region × Nat))
    (present : ∀ g j i k, memBL rs 0 g j = some (i,k) → (regionByte view s g j).isSome = true) :
    Agrees view (mkInputsL s rs (snapshot view s rs)) (σ0L rs) s := by
  apply agrees_σ0L
  intro g j i k tracked
  have same := snapshot_memBL view s rs 0 g j i k tracked
  simp only [Nat.sub_zero] at same
  rw [same]
  cases byte : regionByte view s g j with
  | none => simpa only [byte,Option.isSome_none,Bool.false_eq_true] using present g j i k tracked
  | some b => rfl

theorem snapshot_inputs_length (view : BytePA) (s : St) (rs : List (Region × Nat)) :
    (mkInputsL s rs (snapshot view s rs)).length = totalL rs + 36 :=
  mkInputsG_length s (totalL rs) (snapshot view s rs)

theorem snapshot_bounded (view : BytePA) (s : St) (rs : List (Region × Nat)) :
    (σ0L rs).Bounded (mkInputsL s rs (snapshot view s rs)).length := by
  rw [snapshot_inputs_length]
  exact σ0L_bounded rs

#print axioms snapshot_memBL
#print axioms snapshot_agrees
#print axioms snapshot_inputs_length
#print axioms snapshot_bounded
end ArmCertValue.Physical.Entry
