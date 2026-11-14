import TranslateValue.Width
import TranslateValue.Demo

/-! The width-aware SSA → polynomial translation (byte assembly,): disjoint `orr` is `+`, a
non-overflowing `lsl k` is `2^k·`, and `and [a, imm 2^k−1]` is `a − 2^k·⌊a/2^k⌋` (paired with `lsr k [a]` when
present). Every other op is `symDef`. Sound on the actual table (`symW_sound`). -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TranslateValue
open ArmCertValue

def symDefW (n : Nat) (defs : List Def) (WT : List (Nat × Nat)) (tbl : List Poly) (d : Def) : Poly :=
  let t := tbl.length
  let P := argPoly tbl
  let w := widthArg WT
  match d.op with
  | .orr => match d.args with
    | [a, b] => if (w a).1 ≤ (w b).2 ∨ (w b).1 ≤ (w a).2 then Poly.add (P a) (P b) else Poly.var t
    | _ => Poly.var t
  | .lsl k => match d.args with
    | [a] => if (w a).1 + k ≤ 64 then Poly.scale (2 ^ k) (P a) else symDef n defs tbl d
    | _ => Poly.var t
  | .and => match d.args with
    | [a, .imm m] => match maskBits m with
      | some k => Poly.sub (P a) (Poly.scale (2 ^ k)
          (match findDef (.lsr k) [a] defs 0 with | some j => Poly.var (n + j) | none => Poly.var (BIG + t)))
      | none => Poly.var t
    | _ => Poly.var t
  | _ => symDef n defs tbl d

def symTableW (n : Nat) (defs : List Def) (WT : List (Nat × Nat)) : List Poly :=
  defs.foldl (fun tbl d => tbl ++ [symDefW n defs WT tbl d]) ((List.range n).map Poly.var)

theorem symDefW_sound (n : Nat) (defs : List Def) (WT : List (Nat × Nat)) (tbl : List Poly) (d : Def)
    (env : Nat → Int) (vals : List (BitVec 64))
    (hP : ∀ a ∈ d.args, Poly.eval env (argPoly tbl a) = ((Arg.eval vals a).toNat : Int))
    (hW : ∀ a ∈ d.args, WidthOK (Arg.eval vals a) (widthArg WT a))
    (hv : vals.getD tbl.length 0 = d.op.eval (d.args.map (Arg.eval vals)))
    (hself : env tbl.length = ((vals.getD tbl.length 0).toNat : Int))
    (hq : env (BIG + tbl.length) = (quot vals d : Int))
    (hpartner : ∀ o args j, findDef o args defs 0 = some j →
      env (n + j) = (((o.eval (args.map (Arg.eval vals))).toNat : Nat) : Int))
    (hbool : ∀ c, boolId n defs c = true → (Arg.eval vals c).toNat ≤ 1) :
    Poly.eval env (symDefW n defs WT tbl d) = ((vals.getD tbl.length 0).toNat : Int) := by
  have base := symDef_sound n defs tbl d env vals hP hv hself hq hpartner hbool
  obtain ⟨op, args⟩ := d
  have fallback : Poly.eval env (Poly.var tbl.length) = ((vals.getD tbl.length 0).toNat : Int) := by
    rw [Poly.eval_var, hself]
  cases op <;> simp only [symDefW] <;> (try exact base)
  case orr =>
    split
    · next a b =>
      have ha := hP a (by simp); have hb := hP b (by simp)
      have wa := hW a (by simp); have wb := hW b (by simp)
      have e : Op.eval .orr [Arg.eval vals a, Arg.eval vals b] = Arg.eval vals a ||| Arg.eval vals b := rfl
      split
      · next hdis =>
        simp only [List.map] at hv
        rw [Poly.eval_add, ha, hb, hv, e, BitVec.toNat_or]
        rcases hdis with h | h
        · rw [or_disjoint _ _ (widthArg WT a).1 wa.1
            (Nat.dvd_trans (Nat.pow_dvd_pow 2 h) wb.2)]; simp
        · rw [Nat.or_comm, or_disjoint _ _ (widthArg WT b).1 wb.1
            (Nat.dvd_trans (Nat.pow_dvd_pow 2 h) wa.2)]; simp; omega
      · exact fallback
    · exact fallback
  case lsl k =>
    split
    · next a =>
      split
      · next hk =>
        have ha := hP a (by simp); have wa := hW a (by simp)
        have e : Op.eval (.lsl k) [Arg.eval vals a] = Arg.eval vals a <<< k := rfl
        simp only [List.map] at hv
        have lt : (Arg.eval vals a).toNat * 2 ^ k < 2 ^ 64 := by
          calc (Arg.eval vals a).toNat * 2 ^ k < 2 ^ (widthArg WT a).1 * 2 ^ k :=
                Nat.mul_lt_mul_of_pos_right wa.1 (Nat.two_pow_pos k)
            _ = 2 ^ ((widthArg WT a).1 + k) := (Nat.pow_add _ _ _).symm
            _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hk
        rw [Poly.eval_scale, ha, hv, e, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt lt,
          Int.natCast_mul, Int.natCast_pow, Int.mul_comm]
        rfl
      · exact base
    · exact fallback
  case and =>
    split
    · next a m =>
      split
      · next k hk =>
        have ha := hP a (by simp)
        have e : Op.eval .and [Arg.eval vals a, Arg.eval vals (.imm m)] = Arg.eval vals a &&& m := rfl
        simp only [List.map] at hv
        have hm := maskBits_spec hk
        have val : (vals.getD tbl.length 0).toNat = (Arg.eval vals a).toNat % 2 ^ k := by
          rw [hv, e, BitVec.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod]
        have hquot : (Arg.eval vals a).toNat / 2 ^ k = quot vals ⟨.and, [a, .imm m]⟩ := by
          unfold maskBits at hk
          simp only [quot]
          by_cases he : m.toNat + 1 = 2 ^ Nat.log2 (m.toNat + 1)
          · rw [if_pos he] at hk; cases hk; rw [if_pos he]
          · rw [if_neg he] at hk; cases hk
        rw [Poly.eval_sub, Poly.eval_scale, ha, val]
        have key := Nat.mod_add_div (Arg.eval vals a).toNat (2 ^ k)
        rcases hj : findDef (.lsr k) [a] defs 0 with _ | j
        · simp only [hj]; rw [Poly.eval_var, hq, ← hquot]
          have hp : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := Int.natCast_pow 2 k
          rw [← hp, ← Int.natCast_mul]
          generalize 2 ^ k * ((Arg.eval vals a).toNat / 2 ^ k) = q at key ⊢
          omega
        · simp only [hj]; rw [Poly.eval_var, hpartner _ _ j hj]
          have e2 : Op.eval (.lsr k) [Arg.eval vals a] = Arg.eval vals a >>> k := rfl
          simp only [List.map]
          rw [e2, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
          have hp : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := Int.natCast_pow 2 k
          rw [← hp, ← Int.natCast_mul]
          generalize 2 ^ k * ((Arg.eval vals a).toNat / 2 ^ k) = q at key ⊢
          omega
      · exact fallback
    · exact fallback

/-- The width-aware translation is sound on the actual table (WT = widthTable iw defs, from input widths). -/
theorem symW_sound (inputs : List (BitVec 64)) (defs : List Def) (iw : List (Nat × Nat))
    (hlen : iw.length = inputs.length) (hin : ∀ i, i < inputs.length → WidthOK (inputs.getD i 0) (iw.getD i (64, 0)))
    (wf : WF inputs.length defs = true) (small : inputs.length + defs.length ≤ BIG) :
    ∀ t, t < inputs.length + defs.length →
      (((evalDefs inputs defs).getD t 0).toNat : Int) =
        Poly.eval (envOf inputs.length defs (evalDefs inputs defs))
          ((symTableW inputs.length defs (widthTable iw defs)).getD t (Poly.var t)) := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
  intro ht
  by_cases hn : t < inputs.length
  · have hs : (symTableW inputs.length defs (widthTable iw defs)).getD t (Poly.var t) = Poly.var t := by
      unfold symTableW
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
    let F := fun (tbl : List Poly) (d : Def) => symDefW inputs.length defs (widthTable iw defs) tbl d
    let init := (List.range inputs.length).map Poly.var
    let ptbl := (defs.take k).foldl (fun acc d => acc ++ [F acc d]) init
    have hlen' : ptbl.length = inputs.length + k := by
      simp only [ptbl, init, foldlApp_length, List.length_take, List.length_map, List.length_range]; omega
    have hs : (symTableW inputs.length defs (widthTable iw defs)).getD (inputs.length + k) (Poly.var (inputs.length + k)) =
        symDefW inputs.length defs (widthTable iw defs) ptbl d := by
      have := foldlApp_entry F init defs k (Poly.var (inputs.length + k)) d hd
      simp only [init, List.length_map, List.length_range] at this
      exact this
    rw [hs, ← hlen']
    have pre : ∀ a, a < inputs.length + k → ptbl.getD a (Poly.var a) =
        (symTableW inputs.length defs (widthTable iw defs)).getD a (Poly.var a) := by
      intro a ha
      exact foldlApp_take F init defs k a (Poly.var a) (by omega) (by simpa [init] using ha)
    have widths := width_sound inputs defs iw hlen hin wf
    symm
    apply symDefW_sound inputs.length defs (widthTable iw defs) ptbl d _ (evalDefs inputs defs)
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

#print axioms symW_sound

#print axioms symDefW_sound
end TranslateValue

namespace TranslateValue
open ArmCertValue

def bytesDefs : List Def := [⟨.lsl 8, [.id 1]⟩, ⟨.orr, [.id 0, .id 2]⟩]

/-- Demo (byte assembly): orr (b0, b1 << 8) = b0 + 256·b1 for bytes b0, b1. -/
theorem demo_bytes (b0 b1 : BitVec 64) (h0 : b0.toNat < 2 ^ 8) (h1 : b1.toNat < 2 ^ 8) :
    ((evalDefs [b0, b1] bytesDefs).getD 3 0).toNat = b0.toNat + 256 * b1.toNat := by
  have hin : ∀ i, i < [b0, b1].length → WidthOK ([b0, b1].getD i 0) ([(8, 0), (8, 0)].getD i (64, 0)) := by
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact ⟨h0, by simp⟩
    · exact ⟨h1, by simp⟩
  have wf : WF [b0, b1].length bytesDefs = true := by simp only [List.length_cons, List.length_nil]; decide
  have small : [b0, b1].length + bytesDefs.length ≤ BIG := by simp only [List.length_cons, List.length_nil]; decide
  have h3 := symW_sound [b0, b1] bytesDefs [(8, 0), (8, 0)] rfl hin wf small 3
    (by simp only [List.length_cons, List.length_nil]; decide)
  have c := certified_eq [b0, b1] bytesDefs
    ((symTableW [b0, b1].length bytesDefs (widthTable [(8, 0), (8, 0)] bytesDefs)).getD 3 (Poly.var 3))
    (Poly.add (Poly.var 0) (Poly.scale 256 (Poly.var 1)))
    (by simp only [List.length_cons, List.length_nil]; decide +kernel)
  rw [← h3, Poly.eval_add, Poly.eval_scale, Poly.eval_var, Poly.eval_var,
    env_low _ _ 0 (by decide), env_low _ _ 1 (by decide), input_val _ _ 0 (by simp), input_val _ _ 1 (by simp)] at c
  simp only [List.getD_cons_zero, List.getD_cons_succ] at c
  omega

#print axioms demo_bytes
end TranslateValue
