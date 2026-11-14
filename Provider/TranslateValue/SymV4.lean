import TranslateValue.SymV3

/-! Core v4 byte ops in the normalizer:
* byteAt 0 [a] with bits(a) ≤ 8 is a itself;
* asm8 [0..7] [a,a,...,a] is a (the 8 bytes of a word reassemble it: the STP → LDP round trip);
* asm8 [0,...,0] [a0..a7] with every bits(a_i) ≤ 8 is Σ_i 2^(8i)·a_i (input-byte assembly).
Every other op is `symDef3`. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TranslateValue
open ArmCertValue

def symDef4 (n : Nat) (defs : List Def) (WT : List (Nat × Nat)) (tbl : List Poly) (d : Def) : Poly :=
  let t := tbl.length
  let P := argPoly tbl
  let w := widthArg WT
  match d.op with
  | .byteAt k => match d.args with
    | [a] => if k = 0 ∧ (w a).1 ≤ 8 then P a else Poly.var t
    | _ => Poly.var t
  | .asm8 ks => match ks, d.args with
    | [k0, k1, k2, k3, k4, k5, k6, k7], [a0, a1, a2, a3, a4, a5, a6, a7] =>
      if [k0, k1, k2, k3, k4, k5, k6, k7] = [0, 1, 2, 3, 4, 5, 6, 7] ∧ [a1, a2, a3, a4, a5, a6, a7].all (· = a0) then P a0
      else if [k0, k1, k2, k3, k4, k5, k6, k7].all (· = 0) ∧ [a0, a1, a2, a3, a4, a5, a6, a7].all (fun a => decide ((w a).1 ≤ 8)) then
        Poly.add (P a0) (Poly.add (Poly.scale (2 ^ 8) (P a1)) (Poly.add (Poly.scale (2 ^ 16) (P a2))
          (Poly.add (Poly.scale (2 ^ 24) (P a3)) (Poly.add (Poly.scale (2 ^ 32) (P a4)) (Poly.add (Poly.scale (2 ^ 40) (P a5))
            (Poly.add (Poly.scale (2 ^ 48) (P a6)) (Poly.scale (2 ^ 56) (P a7))))))))
      else Poly.var t
    | _, _ => Poly.var t
  | _ => symDef3 n defs WT tbl d

def symTable4 (n : Nat) (defs : List Def) (WT : List (Nat × Nat)) : List Poly :=
  defs.foldl (fun tbl d => tbl ++ [symDef4 n defs WT tbl d]) ((List.range n).map Poly.var)

theorem symDef4_sound (n : Nat) (defs : List Def) (WT : List (Nat × Nat)) (tbl : List Poly) (d : Def)
    (env : Nat → Int) (vals : List (BitVec 64))
    (hP : ∀ a ∈ d.args, Poly.eval env (argPoly tbl a) = ((Arg.eval vals a).toNat : Int))
    (hW : ∀ a ∈ d.args, WidthOK (Arg.eval vals a) (widthArg WT a))
    (hv : vals.getD tbl.length 0 = d.op.eval (d.args.map (Arg.eval vals)))
    (hself : env tbl.length = ((vals.getD tbl.length 0).toNat : Int))
    (hq : env (BIG + tbl.length) = (quot vals d : Int))
    (hpartner : ∀ o args j, findDef o args defs 0 = some j →
      env (n + j) = (((o.eval (args.map (Arg.eval vals))).toNat : Nat) : Int))
    (hbool : ∀ c, boolId n defs c = true → (Arg.eval vals c).toNat ≤ 1) :
    Poly.eval env (symDef4 n defs WT tbl d) = ((vals.getD tbl.length 0).toNat : Int) := by
  have base := symDef3_sound n defs WT tbl d env vals hP hW hv hself hq hpartner hbool
  obtain ⟨op, args⟩ := d
  have fallback : Poly.eval env (Poly.var tbl.length) = ((vals.getD tbl.length 0).toNat : Int) := by
    rw [Poly.eval_var, hself]
  cases op <;> simp only [symDef4] <;> (try exact base)
  case byteAt k =>
    split
    · next a =>
      split
      · next h =>
        obtain ⟨hk, hw⟩ := h
        subst hk
        have ha := hP a (by simp); have wa := (hW a (by simp)).1
        simp only [List.map] at hv
        rw [ha, hv, byteAt_nat, byteN_zero_small _ (Nat.lt_of_lt_of_le wa (Nat.pow_le_pow_right (by decide) hw))]
      · exact fallback
    · exact fallback
  case asm8 ks =>
    split
    · rename_i k0 k1 k2 k3 k4 k5 k6 k7 a0 a1 a2 a3 a4 a5 a6 a7
      have hP' : ∀ a ∈ [a0, a1, a2, a3, a4, a5, a6, a7], Poly.eval env (argPoly tbl a) = ((Arg.eval vals a).toNat : Int) := hP
      have hW' : ∀ a ∈ [a0, a1, a2, a3, a4, a5, a6, a7], WidthOK (Arg.eval vals a) (widthArg WT a) := hW
      simp only [List.map] at hv
      rw [hv, asm8_nat]
      split
      · next h =>
        obtain ⟨hks, hall⟩ := h
        simp only [List.cons.injEq] at hks
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hks
        have e : ∀ a ∈ [a1, a2, a3, a4, a5, a6, a7], a = a0 := fun a m => by
          simpa using List.all_eq_true.1 hall a m
        rw [e a1 (by simp), e a2 (by simp), e a3 (by simp), e a4 (by simp), e a5 (by simp), e a6 (by simp), e a7 (by simp)]
        rw [hP' a0 (by simp), bytes_reassemble _ (Arg.eval vals a0).isLt]
      · split
        · next _ h =>
          obtain ⟨hks, hw⟩ := h
          have k : ∀ x ∈ [k0, k1, k2, k3, k4, k5, k6, k7], x = 0 := fun x m => by
            simpa using List.all_eq_true.1 hks x m
          have w : ∀ a ∈ [a0, a1, a2, a3, a4, a5, a6, a7], (widthArg WT a).1 ≤ 8 := fun a m => by
            simpa using List.all_eq_true.1 hw a m
          rw [k k0 (by simp), k k1 (by simp), k k2 (by simp), k k3 (by simp), k k4 (by simp), k k5 (by simp),
            k k6 (by simp), k k7 (by simp)]
          have sm : ∀ a ∈ [a0, a1, a2, a3, a4, a5, a6, a7],
              byteN (Arg.eval vals a).toNat 0 = (Arg.eval vals a).toNat := by
            intro a m
            exact byteN_zero_small _ (Nat.lt_of_lt_of_le (hW' a m).1 (Nat.pow_le_pow_right (by decide) (w a m)))
          rw [sm a0 (by simp), sm a1 (by simp), sm a2 (by simp), sm a3 (by simp), sm a4 (by simp),
            sm a5 (by simp), sm a6 (by simp), sm a7 (by simp)]
          rw [Poly.eval_add, Poly.eval_add, Poly.eval_add, Poly.eval_add, Poly.eval_add, Poly.eval_add, Poly.eval_add,
            Poly.eval_scale, Poly.eval_scale, Poly.eval_scale, Poly.eval_scale, Poly.eval_scale, Poly.eval_scale,
            Poly.eval_scale, hP' a0 (by simp), hP' a1 (by simp), hP' a2 (by simp), hP' a3 (by simp), hP' a4 (by simp),
            hP' a5 (by simp), hP' a6 (by simp), hP' a7 (by simp)]
          simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow]
          omega
        · rw [Poly.eval_var, hself, hv, asm8_nat]
    · exact fallback

theorem sym4_sound (inputs : List (BitVec 64)) (defs : List Def) (iw : List (Nat × Nat))
    (hlen : iw.length = inputs.length) (hin : ∀ i, i < inputs.length → WidthOK (inputs.getD i 0) (iw.getD i (64, 0)))
    (wf : WF inputs.length defs = true) (small : inputs.length + defs.length ≤ BIG) :
    ∀ t, t < inputs.length + defs.length →
      (((evalDefs inputs defs).getD t 0).toNat : Int) =
        Poly.eval (envOf inputs.length defs (evalDefs inputs defs))
          ((symTable4 inputs.length defs (widthTable iw defs)).getD t (Poly.var t)) := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
  intro ht
  by_cases hn : t < inputs.length
  · have hs : (symTable4 inputs.length defs (widthTable iw defs)).getD t (Poly.var t) = Poly.var t := by
      unfold symTable4
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
    let F := fun (tbl : List Poly) (d : Def) => symDef4 inputs.length defs (widthTable iw defs) tbl d
    let init := (List.range inputs.length).map Poly.var
    let ptbl := (defs.take k).foldl (fun acc d => acc ++ [F acc d]) init
    have hlen' : ptbl.length = inputs.length + k := by
      simp only [ptbl, init, foldlApp_length, List.length_take, List.length_map, List.length_range]; omega
    have hs : (symTable4 inputs.length defs (widthTable iw defs)).getD (inputs.length + k) (Poly.var (inputs.length + k)) =
        symDef4 inputs.length defs (widthTable iw defs) ptbl d := by
      have := foldlApp_entry F init defs k (Poly.var (inputs.length + k)) d hd
      simp only [init, List.length_map, List.length_range] at this
      exact this
    rw [hs, ← hlen']
    have pre : ∀ a, a < inputs.length + k → ptbl.getD a (Poly.var a) =
        (symTable4 inputs.length defs (widthTable iw defs)).getD a (Poly.var a) := by
      intro a ha
      exact foldlApp_take F init defs k a (Poly.var a) (by omega) (by simpa [init] using ha)
    have widths := width_sound inputs defs iw hlen hin wf
    symm
    apply symDef4_sound inputs.length defs (widthTable iw defs) ptbl d _ (evalDefs inputs defs)
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

#print axioms symDef4_sound
#print axioms sym4_sound
end TranslateValue
