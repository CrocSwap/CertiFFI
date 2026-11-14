import TranslateValue.SymW

/-! Core v3 ops in the normalizer: `sbc3 [a,b,c] = a + ~b + c` as a − b + (2^64−1) + c − 2^64·H
(H = its `sbc3C [a,b,c]` partner when c is boolean, else the quotient), and `cselc cc [n,z,c,v,a,b]` as
W·a + (1−W)·b with W the fresh 0/1 variable BIG + t (env = ConditionHolds). Everything else is `symDefW`. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TranslateValue
open ArmCertValue

def symDef3 (n : Nat) (defs : List Def) (WT : List (Nat × Nat)) (tbl : List Poly) (d : Def) : Poly :=
  let t := tbl.length
  let P := argPoly tbl
  let Q := Poly.var (BIG + t)
  match d.op with
  | .sbc3 => match d.args with
    | [a, b, c] => Poly.sub (Poly.add (Poly.add (Poly.sub (P a) (P b)) (Poly.const (pow64 - 1))) (P c))
        (Poly.scale pow64 (if boolId n defs c then
          (match findDef .sbc3C [a, b, c] defs 0 with | some j => Poly.var (n + j) | none => Q) else Q))
    | _ => Poly.var t
  | .cselc _ => match d.args with
    | [_, _, _, _, a, b] => Poly.add (Poly.mul Q (P a)) (Poly.mul (Poly.sub (Poly.const 1) Q) (P b))
    | _ => Poly.var t
  | _ => symDefW n defs WT tbl d

def symTable3 (n : Nat) (defs : List Def) (WT : List (Nat × Nat)) : List Poly :=
  defs.foldl (fun tbl d => tbl ++ [symDef3 n defs WT tbl d]) ((List.range n).map Poly.var)

theorem symDef3_sound (n : Nat) (defs : List Def) (WT : List (Nat × Nat)) (tbl : List Poly) (d : Def)
    (env : Nat → Int) (vals : List (BitVec 64))
    (hP : ∀ a ∈ d.args, Poly.eval env (argPoly tbl a) = ((Arg.eval vals a).toNat : Int))
    (hW : ∀ a ∈ d.args, WidthOK (Arg.eval vals a) (widthArg WT a))
    (hv : vals.getD tbl.length 0 = d.op.eval (d.args.map (Arg.eval vals)))
    (hself : env tbl.length = ((vals.getD tbl.length 0).toNat : Int))
    (hq : env (BIG + tbl.length) = (quot vals d : Int))
    (hpartner : ∀ o args j, findDef o args defs 0 = some j →
      env (n + j) = (((o.eval (args.map (Arg.eval vals))).toNat : Nat) : Int))
    (hbool : ∀ c, boolId n defs c = true → (Arg.eval vals c).toNat ≤ 1) :
    Poly.eval env (symDef3 n defs WT tbl d) = ((vals.getD tbl.length 0).toNat : Int) := by
  have base := symDefW_sound n defs WT tbl d env vals hP hW hv hself hq hpartner hbool
  obtain ⟨op, args⟩ := d
  have fallback : Poly.eval env (Poly.var tbl.length) = ((vals.getD tbl.length 0).toNat : Int) := by
    rw [Poly.eval_var, hself]
  cases op <;> simp only [symDef3] <;> (try exact base)
  case sbc3 =>
    split
    · next a b c =>
      have ha := hP a (by simp); have hb := hP b (by simp); have hc := hP c (by simp)
      have key := sbc3_nat (Arg.eval vals a) (Arg.eval vals b) (Arg.eval vals c)
      have bb := (Arg.eval vals b).isLt
      simp only [List.map] at hv
      rw [Poly.eval_sub, Poly.eval_add, Poly.eval_add, Poly.eval_sub, Poly.eval_const, Poly.eval_scale, ha, hb, hc, hv]
      split
      · next hcb =>
        rcases hj : findDef .sbc3C [a, b, c] defs 0 with _ | j
        · simp only [hj]; rw [Poly.eval_var, hq]; simp only [quot]; simp only [pow64] at key bb ⊢; omega
        · simp only [hj]; rw [Poly.eval_var, hpartner _ _ j hj]; simp only [List.map]
          rw [sbc3C_nat _ _ _ (hbool c hcb)]; simp only [pow64] at key bb ⊢; omega
      · rw [Poly.eval_var, hq]; simp only [quot]; simp only [pow64] at key bb ⊢; omega
    · exact fallback
  case cselc cc =>
    split
    · next n0 z0 c0 v0 a b =>
      have ha := hP a (by simp); have hb := hP b (by simp)
      simp only [List.map] at hv
      rw [Poly.eval_add, Poly.eval_mul, Poly.eval_mul, Poly.eval_sub, Poly.eval_const, Poly.eval_var, hq, ha, hb, hv,
        cselc_nat]
      simp only [quot]
      split <;> simp
    · exact fallback

theorem sym3_sound (inputs : List (BitVec 64)) (defs : List Def) (iw : List (Nat × Nat))
    (hlen : iw.length = inputs.length) (hin : ∀ i, i < inputs.length → WidthOK (inputs.getD i 0) (iw.getD i (64, 0)))
    (wf : WF inputs.length defs = true) (small : inputs.length + defs.length ≤ BIG) :
    ∀ t, t < inputs.length + defs.length →
      (((evalDefs inputs defs).getD t 0).toNat : Int) =
        Poly.eval (envOf inputs.length defs (evalDefs inputs defs))
          ((symTable3 inputs.length defs (widthTable iw defs)).getD t (Poly.var t)) := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
  intro ht
  by_cases hn : t < inputs.length
  · have hs : (symTable3 inputs.length defs (widthTable iw defs)).getD t (Poly.var t) = Poly.var t := by
      unfold symTable3
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
    let F := fun (tbl : List Poly) (d : Def) => symDef3 inputs.length defs (widthTable iw defs) tbl d
    let init := (List.range inputs.length).map Poly.var
    let ptbl := (defs.take k).foldl (fun acc d => acc ++ [F acc d]) init
    have hlen' : ptbl.length = inputs.length + k := by
      simp only [ptbl, init, foldlApp_length, List.length_take, List.length_map, List.length_range]; omega
    have hs : (symTable3 inputs.length defs (widthTable iw defs)).getD (inputs.length + k) (Poly.var (inputs.length + k)) =
        symDef3 inputs.length defs (widthTable iw defs) ptbl d := by
      have := foldlApp_entry F init defs k (Poly.var (inputs.length + k)) d hd
      simp only [init, List.length_map, List.length_range] at this
      exact this
    rw [hs, ← hlen']
    have pre : ∀ a, a < inputs.length + k → ptbl.getD a (Poly.var a) =
        (symTable3 inputs.length defs (widthTable iw defs)).getD a (Poly.var a) := by
      intro a ha
      exact foldlApp_take F init defs k a (Poly.var a) (by omega) (by simpa [init] using ha)
    have widths := width_sound inputs defs iw hlen hin wf
    symm
    apply symDef3_sound inputs.length defs (widthTable iw defs) ptbl d _ (evalDefs inputs defs)
    · intro x m
      cases x with
      | id a =>
        have := args _ m a rfl
        simp only [argPoly, Arg.eval]
        rw [pre a this]
        exact (ih a this (by omega)).symm
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

#print axioms symDef3_sound
#print axioms sym3_sound
end TranslateValue
