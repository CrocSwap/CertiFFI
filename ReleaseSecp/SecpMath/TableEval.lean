-- Generic SSA row evaluation. No compiler table or native execution is assumed.
import ArmCertValue.Run

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000

namespace SecpMath.TableEval
open ArmCertValue

theorem extend_cons (inputs : List (BitVec 64)) (d : Def) (rest : List Def) :
    extend inputs (d :: rest) = extend (inputs ++ [d.eval inputs]) rest := rfl

/-- Later SSA rows do not overwrite any existing table entry. -/
theorem extend_getD_old (inputs : List (BitVec 64)) (defs : List Def)
    (i : Nat) (inside : i < inputs.length) :
    (extend inputs defs).getD i 0 = inputs.getD i 0 := by
  induction defs generalizing inputs with
  | nil => rfl
  | cons d rest ih =>
    rw [extend_cons, ih (inputs ++ [d.eval inputs]) (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left inside]

/-- The appended row is evaluated only against its actual preceding prefix. -/
theorem extend_getD_row (inputs : List (BitVec 64)) (pre post : List Def) (d : Def) :
    (extend inputs (pre ++ d :: post)).getD (inputs.length + pre.length) 0 =
      d.eval (extend inputs pre) := by
  rw [extend_append, extend_cons]
  have len : (extend inputs pre).length = inputs.length + pre.length := extend_length inputs pre
  rw [extend_getD_old _ post _ (by simp; omega)]
  rw [← len]
  simp

/-- The final table extends the exact table that precedes a row. -/
theorem row_prefix_getD (inputs : List (BitVec 64)) (pre post : List Def) (d : Def)
    (i : Nat) (inside : i < inputs.length + pre.length) :
    (extend inputs (pre ++ d :: post)).getD i 0 = (extend inputs pre).getD i 0 := by
  rw [extend_append]
  exact extend_getD_old _ _ i (by rw [extend_length]; exact inside)

/-- An individual bounded SSA argument sees the same value in prefix and final
tables. This avoids unfolding an entire symbolic program during arithmetic. -/
theorem arg_eval_same {earlier final : List (BitVec 64)} (bound : Nat)
    (same : ∀ i < bound, earlier.getD i 0 = final.getD i 0)
    (a : Arg) (below : a.Below bound) : a.eval earlier = a.eval final := by
  cases a with
  | id i => exact same i below
  | imm value => rfl

theorem def_eval_same {earlier final : List (BitVec 64)} (bound : Nat)
    (same : ∀ i < bound, earlier.getD i 0 = final.getD i 0)
    (d : Def) (below : d.Below bound) : d.eval earlier = d.eval final := by
  unfold Def.eval
  congr 1
  apply List.map_congr_left
  intro a member
  exact arg_eval_same bound same a (below a member)

/-- One row equation expressed entirely in final-table lookups. Its boundedness
and exact position in the actual compiler output remain explicit inputs. -/
theorem final_row_equation (inputs : List (BitVec 64)) (pre post : List Def) (d : Def)
    (below : d.Below (inputs.length + pre.length)) :
    (extend inputs (pre ++ d :: post)).getD (inputs.length + pre.length) 0 =
      d.eval (extend inputs (pre ++ d :: post)) := by
  rw [extend_getD_row]
  apply def_eval_same (inputs.length + pre.length)
  · intro i hi
    exact (row_prefix_getD inputs pre post d i hi).symm
  · exact below

theorem split_at_row (defs : List Def) (i : Nat) (d : Def) (row : defs[i]? = some d) :
    defs = defs.take i ++ d :: defs.drop (i + 1) ∧ (defs.take i).length = i := by
  induction defs generalizing i with
  | nil => simp at row
  | cons head tail ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at row
      subst head
      simp
    | succ i =>
      simp only [List.getElem?_cons_succ] at row
      obtain ⟨split, len⟩ := ih i row
      constructor
      · simpa only [List.take_succ_cons, List.drop_succ_cons, List.cons_append,
          List.cons.injEq, true_and] using split
      · simpa only [List.take_succ_cons, List.length_cons] using congrArg (· + 1) len

/-- Consumer API for a producer's exact row certificate and bounded arguments.
The generic proof never unfolds the actual compiler or evaluates its full table. -/
theorem evalDefs_row (inputs : List (BitVec 64)) (defs : List Def) (i : Nat) (d : Def)
    (row : defs[i]? = some d) (below : d.Below (inputs.length + i)) :
    (evalDefs inputs defs).getD (inputs.length + i) 0 = d.eval (evalDefs inputs defs) := by
  obtain ⟨split, len⟩ := split_at_row defs i d row
  have result := final_row_equation inputs (defs.take i) (defs.drop (i + 1)) d
    (by simpa only [len] using below)
  simpa only [← split, len, evalDefs] using result

#print axioms extend_getD_old
#print axioms extend_getD_row
#print axioms final_row_equation
#print axioms evalDefs_row

end SecpMath.TableEval
