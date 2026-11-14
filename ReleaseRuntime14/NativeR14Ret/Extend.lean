-- (runtime14 P3, RET step facts): indexing lemmas for ArmCertValue.extend (the SSA value table).
import ArmCertPipe.Prefix
set_option autoImplicit false
namespace NativeR14Ret
open ArmCertValue

theorem extend_nil (vals : List (BitVec 64)) : extend vals [] = vals := rfl
theorem extend_cons (vals : List (BitVec 64)) (d : Def) (ds : List Def) :
    extend vals (d :: ds) = extend (vals ++ [d.eval vals]) ds := rfl

theorem extend_length (vals : List (BitVec 64)) (ds : List Def) : (extend vals ds).length = vals.length + ds.length := by
  induction ds generalizing vals with
  | nil => simp [extend_nil]
  | cons d ds ih => rw [extend_cons, ih]; simp; omega

/-- Input positions are unchanged by extend. -/
theorem extend_getD_lt (vals : List (BitVec 64)) (ds : List Def) {i : Nat} (hi : i < vals.length) :
    (extend vals ds).getD i 0 = vals.getD i 0 := by
  obtain ⟨t, ht⟩ := ArmCertPipe.extend_prefix vals ds
  rw [ht]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-- Position vals.length + j holds the value of def j over the table built so far. -/
theorem extend_getD_def (vals : List (BitVec 64)) (ds : List Def) (j : Nat) (hj : j < ds.length) :
    (extend vals ds).getD (vals.length + j) 0 = (ds[j]'hj).eval (extend vals (ds.take j)) := by
  induction ds generalizing vals j with
  | nil => simp at hj
  | cons d ds ih =>
    cases j with
    | zero =>
      rw [extend_cons, extend_getD_lt _ _ (by simp)]
      simp [extend_nil]
    | succ j =>
      rw [extend_cons]
      have := ih (vals ++ [d.eval vals]) j (by simpa using hj)
      simp only [List.length_append, List.length_singleton] at this
      rw [show vals.length + (j + 1) = vals.length + 1 + j by omega, this]
      simp [List.take_succ_cons, extend_cons]

#print axioms extend_getD_def
end NativeR14Ret
