import TranslateValue.Sym

/-! Soundness of the SSA → polynomial translation: on the actual table, every entry's value is its polynomial
evaluated at the environment read off the table (`sym_sound`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace TranslateValue
open ArmCertValue

theorem foldlApp_take {α : Type} (f : List α → Def → α) (init : List α) (defs : List Def) (k i : Nat) (d0 : α)
    (hk : k ≤ defs.length) (hi : i < init.length + k) :
    ((defs.take k).foldl (fun acc d => acc ++ [f acc d]) init).getD i d0 =
      (defs.foldl (fun acc d => acc ++ [f acc d]) init).getD i d0 := by
  have e : defs.foldl (fun acc d => acc ++ [f acc d]) init =
      (defs.drop k).foldl (fun acc d => acc ++ [f acc d]) ((defs.take k).foldl (fun acc d => acc ++ [f acc d]) init) := by
    rw [← List.foldl_append, List.take_append_drop]
  rw [e, foldlApp_prefix f _ (defs.drop k) i d0 (by rw [foldlApp_length, List.length_take]; omega)]

section
variable (inputs : List (BitVec 64)) (defs : List Def)

/-- Every table entry at n + j is its def evaluated on the full table (SSA: id args are earlier ids). -/
theorem vals_entry (wf : WF inputs.length defs = true) (j : Nat) (d : Def) (hd : defs[j]? = some d) :
    (evalDefs inputs defs).getD (inputs.length + j) 0 = d.op.eval (d.args.map (Arg.eval (evalDefs inputs defs))) := by
  have hj : j < defs.length := by
    rcases Nat.lt_or_ge j defs.length with h | h
    · exact h
    · simp [List.getElem?_eq_none h] at hd
  have args : ∀ x ∈ d.args, ∀ i, x = .id i → i < inputs.length + j := by
    have := List.all_eq_true.1 wf j (List.mem_range.2 hj)
    simp only [hd] at this
    intro x m i hx
    have := List.all_eq_true.1 this x m
    subst hx; simpa using this
  unfold evalDefs extend
  rw [foldlApp_entry (fun vals d => d.eval vals) _ _ _ _ _ hd]
  simp only [Def.eval]
  congr 1
  apply List.map_congr_left
  intro x m
  cases x with
  | id i => exact foldlApp_take (fun vals d => d.eval vals) _ _ _ _ _ (by omega) (args _ m i rfl)
  | imm c => rfl

theorem boolDef_le (d : Def) (h : isBoolDef d = true) (xs : List (BitVec 64)) (hxs : xs.length = d.args.length) :
    (d.op.eval xs).toNat ≤ 1 := by
  obtain ⟨op, args⟩ := d
  cases op <;> simp only [isBoolDef, beq_iff_eq, Bool.false_eq_true] at h
  · simp only [decide_eq_true_eq] at h
    show (Op.eval _ xs).toNat ≤ 1
    rw [const_nat]; exact h
  · rw [h] at hxs; match xs, hxs with | [_, _, _], _ => exact b01_le _
  · rw [h] at hxs; match xs, hxs with | [_, _, _], _ => exact b01_le _
  · rw [h] at hxs; match xs, hxs with | [_], _ => exact b01_le _
  · rw [h] at hxs; match xs, hxs with | [_], _ => exact b01_le _
  · rw [h] at hxs; match xs, hxs with | [_, _, _, _], _ => exact b01_le _
  all_goals first
    | (rw [h] at hxs; match xs, hxs with | [_, _, _], _ => exact b01_le _)
    | (rw [h] at hxs; match xs, hxs with | [_, _], _ => exact b01_le _)

theorem bool_val (wf : WF inputs.length defs = true) (x : Arg) (h : boolId inputs.length defs x = true) :
    (Arg.eval (evalDefs inputs defs) x).toNat ≤ 1 := by
  cases x with
  | imm c => simpa [boolId, Arg.eval] using h
  | id c =>
    simp only [boolId] at h
    by_cases hc : c < inputs.length
    · simp [hc] at h
    · simp only [hc, ite_false] at h
      cases hd : defs[c - inputs.length]? with
      | none => simp [hd] at h
      | some d =>
        simp only [hd] at h
        have hc' : c = inputs.length + (c - inputs.length) := by omega
        simp only [Arg.eval]
        rw [hc', vals_entry inputs defs wf _ d hd]
        exact boolDef_le d h _ (by simp)
end

end TranslateValue
