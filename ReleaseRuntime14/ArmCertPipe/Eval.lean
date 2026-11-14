-- d199 pipeline: table-entry evaluation at concrete ids, for the generated ptr lemmas. Side conditions are
-- Boolean (decidable at the literal plan table D), so `simp (disch := decide)` unfolds an entry's definition chain.
import ArmCertPipe.Prefix
set_option autoImplicit false
namespace ArmCertPipe
open ArmCertValue

/-- Arguments of a definition all point below `i` (Boolean). -/
def belowB (i : Nat) (d : Def) : Bool := d.args.all fun a => match a with | .id n => decide (n < i) | .imm _ => true

theorem below_of_belowB {i : Nat} {d : Def} (h : belowB i d = true) : d.Below i := by
  intro a ha
  have := List.all_eq_true.1 h a ha
  cases a with
  | id n => simpa [Arg.Below] using this
  | imm c => simp [Arg.Below]

theorem getD_input_at {vals : List (BitVec 64)} {ds : List Def} {N : Nat} (hN : vals.length = N) (i : Nat)
    (hi : decide (i < N) = true) : (extend vals ds).getD i 0 = vals.getD i 0 :=
  getD_extend_input vals ds (by rw [hN]; simpa using hi)

theorem getD_def_at {vals : List (BitVec 64)} {ds : List Def} {N : Nat} (hN : vals.length = N) (i : Nat)
    (hi : decide (N ≤ i ∧ i - N < ds.length) = true) (hb : belowB i (ds.getD (i - N) ⟨.add, []⟩) = true) :
    (extend vals ds).getD i 0 = (ds.getD (i - N) ⟨.add, []⟩).eval (extend vals ds) := by
  simp only [decide_eq_true_eq] at hi
  obtain ⟨hle, hlt⟩ := hi
  obtain ⟨j, rfl⟩ : ∃ j, i = N + j := ⟨i - N, by omega⟩
  simp only [Nat.add_sub_cancel_left] at hlt hb ⊢
  have e : ds.getD j ⟨.add, []⟩ = ds[j] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  rw [e] at hb ⊢
  rw [← hN]
  exact getD_extend_def vals ds hlt (by rw [hN]; exact below_of_belowB hb)

#print axioms getD_input_at
#print axioms getD_def_at
end ArmCertPipe
