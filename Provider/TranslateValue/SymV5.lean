import TranslateValue.SymV4

/-! H-P1 rules: (a) constant folding: when every argument's polynomial is a constant, the entry is the op
evaluated on those constants (sound for every op); (b) carry conditions: `cond 2/3 [n,z,c,v]` (CS/CC) is c / 1−c
and `cselc 2/3 [n,z,c,v,a,b]` selects with W = c / 1−c, when c is a boolean id. Everything else is `symDef4`. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TranslateValue
open ArmCertValue

/-- `some c` when the polynomial is (after normalizing and dropping zero terms) the constant c. -/
def Poly.asConst (p : Poly) : Option Int :=
  match (Poly.normalize p).filter (fun t => t.1 != 0) with
  | [] => some 0
  | [(c, [])] => some c
  | _ => none

theorem Poly.eval_filter_nonzero (env : Nat → Int) (q : Poly) :
    Poly.eval env (q.filter (fun t => t.1 != 0)) = Poly.eval env q := by
  induction q with
  | nil => rfl
  | cons t q ih =>
    by_cases h : t.1 = 0
    · rw [List.filter_cons_of_neg (by simp [h]), ih, Poly.eval_cons, h]; simp
    · rw [List.filter_cons_of_pos (by simp [h]), Poly.eval_cons, Poly.eval_cons, ih]

theorem Poly.eval_asConst {p : Poly} {c : Int} (h : Poly.asConst p = some c) (env : Nat → Int) :
    Poly.eval env p = c := by
  rw [← Poly.eval_normalize, ← Poly.eval_filter_nonzero]
  unfold Poly.asConst at h
  split at h
  · next he => cases h; rw [he]; rfl
  · next c' he => cases h; rw [he]; simp [Poly.eval, Mono.eval]
  · cases h

def constsOf (tbl : List Poly) : List Arg → Option (List Int)
  | [] => some []
  | a :: as => match Poly.asConst (argPoly tbl a), constsOf tbl as with
    | some c, some cs => some (c :: cs)
    | _, _ => none

theorem constsOf_vals (tbl : List Poly) (env : Nat → Int) (vals : List (BitVec 64)) :
    ∀ (args : List Arg) (cs : List Int), constsOf tbl args = some cs →
      (∀ a ∈ args, Poly.eval env (argPoly tbl a) = ((Arg.eval vals a).toNat : Int)) →
      args.map (Arg.eval vals) = cs.map (fun c => BitVec.ofInt 64 c)
  | [], cs, h, _ => by simp [constsOf] at h; subst h; rfl
  | a :: as, cs, h, hP => by
    unfold constsOf at h
    split at h
    · next c cs' hc hcs =>
      cases h
      have ha := hP a (by simp)
      rw [Poly.eval_asConst hc] at ha
      have rest := constsOf_vals tbl env vals as cs' hcs (fun x m => hP x (List.mem_cons_of_mem a m))
      simp only [List.map_cons, rest, List.cons.injEq, and_true]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofInt]
      have hlt := (Arg.eval vals a).isLt
      omega
    · cases h

/-- W for a CS/CC condition on a boolean C flag. -/
def carryW (tbl : List Poly) (cc : BitVec 4) (cf : Arg) : Poly :=
  if cc = 2 then argPoly tbl cf else Poly.sub (Poly.const 1) (argPoly tbl cf)

def symDef5 (n : Nat) (defs : List Def) (WT : List (Nat × Nat)) (tbl : List Poly) (d : Def) : Poly :=
  match constsOf tbl d.args with
  | some cs => Poly.const (d.op.eval (cs.map (fun c => BitVec.ofInt 64 c))).toNat
  | none =>
    match d.op with
    | .cond cc => match d.args with
      | [_, _, cf, _] => if (cc = 2 ∨ cc = 3) ∧ boolId n defs cf then carryW tbl cc cf else symDef4 n defs WT tbl d
      | _ => symDef4 n defs WT tbl d
    | .cselc cc => match d.args with
      | [_, _, cf, _, a, b] => if (cc = 2 ∨ cc = 3) ∧ boolId n defs cf then
          Poly.add (Poly.mul (carryW tbl cc cf) (argPoly tbl a))
            (Poly.mul (Poly.sub (Poly.const 1) (carryW tbl cc cf)) (argPoly tbl b))
        else symDef4 n defs WT tbl d
      | _ => symDef4 n defs WT tbl d
    | _ => symDef4 n defs WT tbl d

theorem condHolds_cs (n z cf v : BitVec 64) (h : cf.toNat ≤ 1) :
    (b01 (condHolds 2 n z cf v)).toNat = cf.toNat := by
  have : condHolds 2 n z cf v = (cf != 0) := by simp [condHolds]
  rw [this]
  by_cases hc : cf = 0
  · subst hc; rfl
  · have h1 : cf.toNat = 1 := by
      have : cf.toNat ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
      omega
    have hc' : ¬ cf = 0#64 := hc
    simp [hc', b01, h1]

theorem condHolds_cc (n z cf v : BitVec 64) (h : cf.toNat ≤ 1) :
    ((b01 (condHolds 3 n z cf v)).toNat : Int) = 1 - (cf.toNat : Int) := by
  have : condHolds 3 n z cf v = !(cf != 0) := by simp [condHolds]
  rw [this]
  by_cases hc : cf = 0
  · subst hc; rfl
  · have h1 : cf.toNat = 1 := by
      have : cf.toNat ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
      omega
    have hc' : ¬ cf = 0#64 := hc
    simp [hc', b01, h1]

theorem carryW_eval (tbl : List Poly) (env : Nat → Int) (vals : List (BitVec 64)) (cc : BitVec 4) (cf : Arg)
    (hcc : cc = 2 ∨ cc = 3) (hb : (Arg.eval vals cf).toNat ≤ 1)
    (hP : Poly.eval env (argPoly tbl cf) = ((Arg.eval vals cf).toNat : Int)) (n z v : BitVec 64) :
    Poly.eval env (carryW tbl cc cf) = ((b01 (condHolds cc n z (Arg.eval vals cf) v)).toNat : Int) := by
  rcases hcc with rfl | rfl
  · unfold carryW; rw [if_pos rfl, hP, condHolds_cs _ _ _ _ hb]
  · unfold carryW; rw [if_neg (by decide), Poly.eval_sub, Poly.eval_const, hP, condHolds_cc _ _ _ _ hb]

def symTable5 (n : Nat) (defs : List Def) (WT : List (Nat × Nat)) : List Poly :=
  defs.foldl (fun tbl d => tbl ++ [symDef5 n defs WT tbl d]) ((List.range n).map Poly.var)

theorem symDef5_sound (n : Nat) (defs : List Def) (WT : List (Nat × Nat)) (tbl : List Poly) (d : Def)
    (env : Nat → Int) (vals : List (BitVec 64))
    (hP : ∀ a ∈ d.args, Poly.eval env (argPoly tbl a) = ((Arg.eval vals a).toNat : Int))
    (hW : ∀ a ∈ d.args, WidthOK (Arg.eval vals a) (widthArg WT a))
    (hv : vals.getD tbl.length 0 = d.op.eval (d.args.map (Arg.eval vals)))
    (hself : env tbl.length = ((vals.getD tbl.length 0).toNat : Int))
    (hq : env (BIG + tbl.length) = (quot vals d : Int))
    (hpartner : ∀ o args j, findDef o args defs 0 = some j →
      env (n + j) = (((o.eval (args.map (Arg.eval vals))).toNat : Nat) : Int))
    (hbool : ∀ c, boolId n defs c = true → (Arg.eval vals c).toNat ≤ 1) :
    Poly.eval env (symDef5 n defs WT tbl d) = ((vals.getD tbl.length 0).toNat : Int) := by
  have base := symDef4_sound n defs WT tbl d env vals hP hW hv hself hq hpartner hbool
  unfold symDef5
  split
  · next cs hcs =>
    rw [Poly.eval_const, hv, constsOf_vals tbl env vals d.args cs hcs hP]
  · rename_i hnone
    obtain ⟨op, args⟩ := d
    cases op <;> simp only <;> (try exact base)
    case cond cc =>
      split
      · next n0 z0 cf v0 =>
        split
        · next h =>
          obtain ⟨hcc, hb⟩ := h
          have e : Op.eval (.cond cc) [Arg.eval vals n0, Arg.eval vals z0, Arg.eval vals cf, Arg.eval vals v0] =
              b01 (condHolds cc (Arg.eval vals n0) (Arg.eval vals z0) (Arg.eval vals cf) (Arg.eval vals v0)) := rfl
          simp only [List.map] at hv
          rw [hv, e, carryW_eval tbl env vals cc cf hcc (hbool cf hb) (hP cf (by simp))]
        · exact base
      · exact base
    case cselc cc =>
      split
      · next n0 z0 cf v0 a b =>
        split
        · next h =>
          obtain ⟨hcc, hb⟩ := h
          have e : Op.eval (.cselc cc) [Arg.eval vals n0, Arg.eval vals z0, Arg.eval vals cf, Arg.eval vals v0,
              Arg.eval vals a, Arg.eval vals b] =
              if condHolds cc (Arg.eval vals n0) (Arg.eval vals z0) (Arg.eval vals cf) (Arg.eval vals v0)
              then Arg.eval vals a else Arg.eval vals b := rfl
          simp only [List.map] at hv
          rw [hv, e, Poly.eval_add, Poly.eval_mul, Poly.eval_mul, Poly.eval_sub, Poly.eval_const,
            carryW_eval tbl env vals cc cf hcc (hbool cf hb) (hP cf (by simp)) (Arg.eval vals n0) (Arg.eval vals z0)
              (Arg.eval vals v0),
            hP a (by simp), hP b (by simp)]
          by_cases hc : condHolds cc (Arg.eval vals n0) (Arg.eval vals z0) (Arg.eval vals cf) (Arg.eval vals v0) <;>
            simp [hc, b01]
        · exact base
      · exact base

theorem sym5_sound (inputs : List (BitVec 64)) (defs : List Def) (iw : List (Nat × Nat))
    (hlen : iw.length = inputs.length) (hin : ∀ i, i < inputs.length → WidthOK (inputs.getD i 0) (iw.getD i (64, 0)))
    (wf : WF inputs.length defs = true) (small : inputs.length + defs.length ≤ BIG) :
    ∀ t, t < inputs.length + defs.length →
      (((evalDefs inputs defs).getD t 0).toNat : Int) =
        Poly.eval (envOf inputs.length defs (evalDefs inputs defs))
          ((symTable5 inputs.length defs (widthTable iw defs)).getD t (Poly.var t)) := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
  intro ht
  by_cases hn : t < inputs.length
  · have hs : (symTable5 inputs.length defs (widthTable iw defs)).getD t (Poly.var t) = Poly.var t := by
      unfold symTable5
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
    let F := fun (tbl : List Poly) (d : Def) => symDef5 inputs.length defs (widthTable iw defs) tbl d
    let init := (List.range inputs.length).map Poly.var
    let ptbl := (defs.take k).foldl (fun acc d => acc ++ [F acc d]) init
    have hlen' : ptbl.length = inputs.length + k := by
      simp only [ptbl, init, foldlApp_length, List.length_take, List.length_map, List.length_range]; omega
    have hs : (symTable5 inputs.length defs (widthTable iw defs)).getD (inputs.length + k) (Poly.var (inputs.length + k)) =
        symDef5 inputs.length defs (widthTable iw defs) ptbl d := by
      have := foldlApp_entry F init defs k (Poly.var (inputs.length + k)) d hd
      simp only [init, List.length_map, List.length_range] at this
      exact this
    rw [hs, ← hlen']
    have pre : ∀ a, a < inputs.length + k → ptbl.getD a (Poly.var a) =
        (symTable5 inputs.length defs (widthTable iw defs)).getD a (Poly.var a) := by
      intro a ha
      exact foldlApp_take F init defs k a (Poly.var a) (by omega) (by simpa [init] using ha)
    have widths := width_sound inputs defs iw hlen hin wf
    symm
    apply symDef5_sound inputs.length defs (widthTable iw defs) ptbl d _ (evalDefs inputs defs)
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

#print axioms symDef5_sound
#print axioms sym5_sound
end TranslateValue
