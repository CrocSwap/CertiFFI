import TranslateValue.SymDefSound

/-! The SSA → polynomial translation is sound on the actual value table (`sym_sound`), and the per-kernel
certificate check (`certified_eq`): if the kernel decides `isZero (Σ c_i·P_{o_i} − T − K)` then the actual
outputs satisfy the integer identity Σ c_i·out_i = eval T + eval K. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace TranslateValue
open ArmCertValue

section
variable (inputs : List (BitVec 64)) (defs : List Def)

theorem env_low (i : Nat) (hi : i < BIG) :
    envOf inputs.length defs (evalDefs inputs defs) i = (((evalDefs inputs defs).getD i 0).toNat : Int) := by
  simp [envOf, hi]

theorem env_quot (k : Nat) (d : Def) (hd : defs[k]? = some d) :
    envOf inputs.length defs (evalDefs inputs defs) (BIG + (inputs.length + k)) = (quot (evalDefs inputs defs) d : Int) := by
  have h1 : ¬ BIG + (inputs.length + k) < BIG := by omega
  have h2 : BIG + (inputs.length + k) - BIG - inputs.length = k := by omega
  simp [envOf, h1, h2, hd]

theorem sym_sound (wf : WF inputs.length defs = true) (small : inputs.length + defs.length ≤ BIG) :
    ∀ t, t < inputs.length + defs.length →
      (((evalDefs inputs defs).getD t 0).toNat : Int) =
        Poly.eval (envOf inputs.length defs (evalDefs inputs defs)) ((symTable inputs.length defs).getD t (Poly.var t)) := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
  intro ht
  by_cases hn : t < inputs.length
  · have hs : (symTable inputs.length defs).getD t (Poly.var t) = Poly.var t := by
      unfold symTable
      rw [foldlApp_prefix _ _ _ _ _ (by simpa using hn)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hn]
    rw [hs, Poly.eval_var, env_low inputs defs t (by omega)]
  · obtain ⟨k, rfl⟩ : ∃ k, t = inputs.length + k := ⟨t - inputs.length, by omega⟩
    have hk : k < defs.length := by omega
    obtain ⟨d, hd⟩ : ∃ d, defs[k]? = some d := ⟨defs[k], List.getElem?_eq_getElem hk⟩
    have args : ∀ x ∈ d.args, ∀ a, x = .id a → a < inputs.length + k := by
      have := List.all_eq_true.1 wf k (List.mem_range.2 hk)
      simp only [hd] at this
      intro x m a hx
      have := List.all_eq_true.1 this x m
      subst hx; simpa using this
    let F := fun (tbl : List Poly) (d : Def) => symDef inputs.length defs tbl d
    let init := (List.range inputs.length).map Poly.var
    let ptbl := (defs.take k).foldl (fun acc d => acc ++ [F acc d]) init
    have hlen : ptbl.length = inputs.length + k := by
      simp only [ptbl, init, foldlApp_length, List.length_take, List.length_map, List.length_range]; omega
    have hs : (symTable inputs.length defs).getD (inputs.length + k) (Poly.var (inputs.length + k)) =
        symDef inputs.length defs ptbl d := by
      have := foldlApp_entry F init defs k (Poly.var (inputs.length + k)) d hd
      simp only [init, List.length_map, List.length_range] at this
      exact this
    rw [hs, ← hlen]
    have pre : ∀ a, a < inputs.length + k → ptbl.getD a (Poly.var a) = (symTable inputs.length defs).getD a (Poly.var a) := by
      intro a ha
      exact foldlApp_take F init defs k a (Poly.var a) (by omega) (by simpa [init] using ha)
    symm
    apply symDef_sound inputs.length defs ptbl d _ (evalDefs inputs defs)
    · intro x m
      cases x with
      | id a =>
        have := args _ m a rfl
        simp only [argPoly, Arg.eval]
        rw [pre a this]
        exact (ih a this (by omega)).symm
      | imm c => simp [argPoly, Arg.eval, Poly.eval_const]
    · rw [hlen]; exact vals_entry inputs defs wf k d hd
    · rw [hlen]; exact env_low inputs defs _ (by omega)
    · rw [hlen]; exact env_quot inputs defs k d hd
    · intro o as j hj
      obtain ⟨_, hj'⟩ := findDef_spec o as defs 0 j hj
      simp only [Nat.sub_zero] at hj'
      have jlt : j < defs.length := by
        rcases Nat.lt_or_ge j defs.length with h | h
        · exact h
        · simp [List.getElem?_eq_none h] at hj'
      rw [env_low inputs defs _ (by omega), vals_entry inputs defs wf j _ hj']
    · intro c hc; exact bool_val inputs defs wf c hc
end

/-- The per-kernel certificate check: the kernel-decided zero test gives an integer identity on the actual
    table values (env read off the table). -/
theorem certified_eq (inputs : List (BitVec 64)) (defs : List Def) (lhs rhs : Poly)
    (check : Poly.isZero (Poly.sub lhs rhs) = true) :
    Poly.eval (envOf inputs.length defs (evalDefs inputs defs)) lhs =
      Poly.eval (envOf inputs.length defs (evalDefs inputs defs)) rhs := by
  have := Poly.eval_of_isZero check (envOf inputs.length defs (evalDefs inputs defs))
  rw [Poly.eval_sub] at this; omega

#print axioms sym_sound
#print axioms certified_eq
end TranslateValue
