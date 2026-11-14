import TranslateValue.SymV5
import TranslateValue.FastPoly

/-! Literal tables, checked entry by entry. The kernel cannot evaluate the append-fold tables (`widthTable`,
`symTable5`) over a 700-entry SSA table: the accumulator is re-evaluated at every lookup. Instead a generator
supplies the tables as literals and the kernel checks each entry locally against the one-step rule:
`checkW` (widths, syntactic equality, giving `widthTable iw defs = W`) and `checkP` (polynomials, equality as
polynomials via the merge-sort normal form, giving value = eval of the literal entry on the actual table). -/

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace TranslateValue
open ArmCertValue

/-- A table built by the append-fold equals a literal L that satisfies the one-step rule entrywise. -/
theorem foldlApp_eq_of_local {α : Type} (F : List α → Def → α) (init : List α) (defs : List Def) (L : List α)
    (hlen : L.length = init.length + defs.length) (hinit : L.take init.length = init)
    (hloc : ∀ k (h : k < defs.length), L[init.length + k]? = some (F (L.take (init.length + k)) defs[k])) :
    defs.foldl (fun acc d => acc ++ [F acc d]) init = L := by
  have step : ∀ k, k ≤ defs.length → (defs.take k).foldl (fun acc d => acc ++ [F acc d]) init = L.take (init.length + k) := by
    intro k
    induction k with
    | zero => intro _; simpa using hinit.symm
    | succ k ih =>
      intro hk
      have hk' : k < defs.length := by omega
      rw [List.take_add_one, List.getElem?_eq_getElem hk', Option.toList_some, List.foldl_append, ih (by omega),
        List.foldl_cons, List.foldl_nil, ← Nat.add_assoc, List.take_add_one, hloc k hk', Option.toList_some]
  have := step defs.length (Nat.le_refl _)
  rw [List.take_length] at this
  rw [this, ← hlen, List.take_length]

def headW (iw : List (Nat × Nat)) (defs : List Def) (W : List (Nat × Nat)) : Bool :=
  W.length == iw.length + defs.length && W.take iw.length == iw

def entryW (iw : List (Nat × Nat)) (defs : List Def) (W : List (Nat × Nat)) (k : Nat) : Bool :=
  match defs[k]? with
  | some d => W[iw.length + k]? == some (widthDef (W.take (iw.length + k)) d)
  | none => false

theorem checkW_eq (iw : List (Nat × Nat)) (defs : List Def) (W : List (Nat × Nat)) (h0 : headW iw defs W = true)
    (h : ∀ k, k < defs.length → entryW iw defs W k = true) : widthTable iw defs = W := by
  simp only [headW, Bool.and_eq_true, beq_iff_eq] at h0
  obtain ⟨hl, hi⟩ := h0
  unfold widthTable
  apply foldlApp_eq_of_local (fun W d => widthDef W d) iw defs W hl hi
  intro k hk'
  have := h k hk'
  simp only [entryW, List.getElem?_eq_getElem hk'] at this
  simpa using this

/-- Chunked discharge of `∀ k < n, f k`: each chunk is its own kernel check (the kernel's caches grow within
    one check), chained by this step lemma. -/
theorem allLt_step (f : Nat → Bool) (a b : Nat) (h1 : ∀ k, k < a → f k = true) (h2 : (List.range' a b).all f = true) :
    ∀ k, k < a + b → f k = true := by
  intro k hk
  by_cases ha : k < a
  · exact h1 k ha
  · exact List.all_eq_true.1 h2 k (List.mem_range'_1.2 ⟨by omega, by omega⟩)

theorem allLt_zero (f : Nat → Bool) : ∀ k, k < 0 → f k = true := fun _ h => absurd h (Nat.not_lt_zero _)

def headP (n : Nat) (defs : List Def) (L : List Poly) : Bool :=
  L.length == n + defs.length && ((List.range n).all fun i => L.getD i [] == Poly.var i)

/-- Entry n + k agrees, as a polynomial, with the one-step rule on the literal prefix. -/
def entryP (n : Nat) (defs : List Def) (WT : List (Nat × Nat)) (L : List Poly) (k : Nat) : Bool :=
  match defs[k]? with
  | some d => Poly.eqF (L.getD (n + k) []) (symDef5 n defs WT (L.take (n + k)) d)
  | none => false

theorem checkP_sound (inputs : List (BitVec 64)) (defs : List Def) (iw WT : List (Nat × Nat)) (L : List Poly)
    (hlen : iw.length = inputs.length) (hin : ∀ i, i < inputs.length → WidthOK (inputs.getD i 0) (iw.getD i (64, 0)))
    (wf : WF inputs.length defs = true) (small : inputs.length + defs.length ≤ BIG)
    (hWT : widthTable iw defs = WT) (h0 : headP inputs.length defs L = true)
    (hent : ∀ k, k < defs.length → entryP inputs.length defs WT L k = true) :
    ∀ t, t < inputs.length + defs.length →
      (((evalDefs inputs defs).getD t 0).toNat : Int) =
        Poly.eval (envOf inputs.length defs (evalDefs inputs defs)) (L.getD t []) := by
  simp only [headP, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h0
  obtain ⟨hL, hvar⟩ := h0
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
  intro ht
  by_cases hn : t < inputs.length
  · rw [hvar t hn, Poly.eval_var, env_low inputs defs t (by omega)]
  · obtain ⟨k, rfl⟩ : ∃ k, t = inputs.length + k := ⟨t - inputs.length, by omega⟩
    have hk : k < defs.length := by omega
    obtain ⟨d, hd⟩ : ∃ d, defs[k]? = some d := ⟨defs[k], List.getElem?_eq_getElem hk⟩
    have args : ∀ x ∈ d.args, ∀ a, x = .id a → a < inputs.length + k := by
      have := List.all_eq_true.1 wf k (List.mem_range.2 hk)
      simp only [hd] at this
      intro x m a hx
      have := List.all_eq_true.1 this x m
      subst hx; simpa using this
    have he := hent k hk
    simp only [entryP, hd] at he
    rw [Poly.eval_of_eqF he]
    let ptbl := L.take (inputs.length + k)
    have hlen' : ptbl.length = inputs.length + k := by simp only [ptbl, List.length_take]; omega
    have widths := width_sound inputs defs iw hlen hin wf
    rw [hWT] at widths
    have key := symDef5_sound inputs.length defs WT ptbl d (envOf inputs.length defs (evalDefs inputs defs))
      (evalDefs inputs defs) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hlen'] at key; exact key.symm
    · intro x m
      cases x with
      | id a =>
        have ha := args _ m a rfl
        simp only [argPoly, Arg.eval]
        have : ptbl.getD a (Poly.var a) = L.getD a [] := by
          simp only [ptbl, List.getD_eq_getElem?_getD, List.getElem?_take, ha, ↓reduceIte]
          rw [List.getElem?_eq_getElem (by omega)]; rfl
        rw [this]
        exact (ih a ha (by omega)).symm
      | imm c => simp [argPoly, Arg.eval, Poly.eval_const]
    · intro x m
      cases x with
      | id a =>
        have := args _ m a rfl
        simp only [widthArg, Arg.eval]
        exact widths a (by omega)
      | imm c => exact immBits_ok c
    · rw [hlen']; exact vals_entry inputs defs wf k d hd
    · rw [hlen']; exact env_low inputs defs _ (by omega)
    · rw [hlen']; exact env_quot inputs defs k d hd
    · intro o as j hj
      obtain ⟨_, hj'⟩ := findDef_spec o as defs 0 j hj
      simp only [Nat.sub_zero] at hj'
      have jlt : j < defs.length := by
        rcases Nat.lt_or_ge j defs.length with h | h
        · exact h
        · simp [List.getElem?_eq_none h] at hj'
      rw [env_low inputs defs _ (by omega), vals_entry inputs defs wf j _ hj']
    · intro c hc; exact bool_val inputs defs wf c hc

/-- One SSA entry is well formed (every id argument is earlier). -/
def wfAt (n : Nat) (defs : List Def) (k : Nat) : Bool :=
  match defs[k]? with
  | some d => d.args.all (fun x => match x with | .id i => decide (i < n + k) | .imm _ => true)
  | none => true

theorem WF_of_all (n : Nat) (defs : List Def) (h : ∀ k, k < defs.length → wfAt n defs k = true) : WF n defs = true := by
  unfold WF
  rw [List.all_eq_true]
  intro k hk
  exact h k (List.mem_range.1 hk)

#print axioms foldlApp_eq_of_local
#print axioms checkW_eq
#print axioms checkP_sound
end TranslateValue
