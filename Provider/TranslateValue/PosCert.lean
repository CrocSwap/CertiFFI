import TranslateValue.TableLit
import TranslateValue.Bound

/-! ArmCert value layer, normalizer: the generic BOUND checker over a literal table.
Atoms are polynomials known to be ≥ 0 on the actual table: an entry's value (`val`), its width slack
2^bits − 1 − value (`wid`), the slack 1 − value of a boolean-producing entry (`bit`), and a quotient
variable (`quot`). Certificate expressions (`PE`) are sums and products of atoms and Nat constants, hence ≥ 0.
A certificate tree case-splits boolean entries by substitution and ends in leaves that show
k·T − e is a nonnegative constant (so T ≥ 0), or refute the branch (e is a negative constant). -/

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace TranslateValue
open ArmCertValue

/-- The literal tables a certificate refers to. -/
structure Ctx where
  n : Nat
  defs : List Def
  W : List (Nat × Nat)
  L : List Poly

def Ctx.isBool (c : Ctx) (t : Nat) : Bool :=
  decide (c.n ≤ t) && match c.defs[t - c.n]? with | some d => isBoolDef d | none => false

inductive Atom where
  | val (t : Nat)
  | wid (t : Nat)
  | bit (t : Nat)
  | quot (t : Nat)

def Atom.poly (c : Ctx) : Atom → Poly
  | .val t => c.L.getD t []
  | .wid t => Poly.sub (Poly.const ((2 : Int) ^ (c.W.getD t (64, 0)).1 - 1)) (c.L.getD t [])
  | .bit t => if c.isBool t then Poly.sub (Poly.const 1) (c.L.getD t []) else []
  | .quot t => Poly.var (BIG + t)

inductive PE where
  | atom (a : Atom)
  | const (k : Nat)
  | add (a b : PE)
  | mul (a b : PE)

def PE.poly (c : Ctx) : PE → Poly
  | .atom a => a.poly c
  | .const k => Poly.const k
  | .add a b => Poly.add (a.poly c) (b.poly c)
  | .mul a b => Poly.mul (a.poly c) (b.poly c)

/-- What the checker needs from the environment: atoms are ≥ 0 and boolean entries are 0/1. -/
structure Ctx.Sound (c : Ctx) (env : Nat → Int) : Prop where
  atom : ∀ a : Atom, 0 ≤ Poly.eval env (a.poly c)
  bool : ∀ t, c.isBool t = true → 0 ≤ env t ∧ env t ≤ 1

theorem PE.nonneg (c : Ctx) (env : Nat → Int) (hs : c.Sound env) : ∀ e : PE, 0 ≤ Poly.eval env (e.poly c)
  | .atom a => hs.atom a
  | .const k => by simp [PE.poly, Poly.eval_const]
  | .add a b => by
    simp only [PE.poly]; rw [Poly.eval_add]
    have := PE.nonneg c env hs a; have := PE.nonneg c env hs b; omega
  | .mul a b => by
    simp only [PE.poly]; rw [Poly.eval_mul]
    exact Int.mul_nonneg (PE.nonneg c env hs a) (PE.nonneg c env hs b)

def substAll (subs : List (Nat × Int)) (p : Poly) : Poly := subs.foldl (fun p s => Poly.subst s.1 s.2 p) p

theorem eval_substAll (env : Nat → Int) : ∀ (subs : List (Nat × Int)) (p : Poly), (∀ s ∈ subs, env s.1 = s.2) →
    Poly.eval env (substAll subs p) = Poly.eval env p
  | [], _, _ => rfl
  | s :: subs, p, h => by
    have := eval_substAll env subs (Poly.subst s.1 s.2 p) (fun x m => h x (List.mem_cons_of_mem s m))
    simp only [substAll, List.foldl_cons] at *
    rw [this, Poly.eval_subst env s.1 s.2 (h s List.mem_cons_self)]

inductive Cert where
  | leaf (k : Nat) (e : PE)
  | refute (e : PE)
  | split (v : Nat) (c0 c1 : Cert)

def Cert.check (c : Ctx) (T : Poly) : List (Nat × Int) → Cert → Bool
  | subs, .leaf k e => decide (0 < k) && Poly.constNonnegF (substAll subs (Poly.sub (Poly.scale k T) (e.poly c)))
  | subs, .refute e => Poly.constNegF (substAll subs (e.poly c))
  | subs, .split v c0 c1 => c.isBool v && Cert.check c T ((v, 0) :: subs) c0 && Cert.check c T ((v, 1) :: subs) c1

theorem Cert.sound (c : Ctx) (env : Nat → Int) (hs : c.Sound env) (T : Poly) :
    ∀ (subs : List (Nat × Int)) (ce : Cert), Cert.check c T subs ce = true → (∀ s ∈ subs, env s.1 = s.2) →
      0 ≤ Poly.eval env T
  | subs, .leaf k e, h, hsub => by
    simp only [Cert.check, Bool.and_eq_true, decide_eq_true_eq] at h
    have r := Poly.eval_of_constNonnegF h.2 env
    rw [eval_substAll env subs _ hsub, Poly.eval_sub, Poly.eval_scale] at r
    have he := PE.nonneg c env hs e
    have hk : (0 : Int) < k := by exact_mod_cast h.1
    have : 0 ≤ (k : Int) * Poly.eval env T := by omega
    rcases Int.lt_or_le (Poly.eval env T) 0 with hn | hn
    · have := Int.mul_lt_mul_of_pos_left hn hk; simp at this; omega
    · exact hn
  | subs, .refute e, h, hsub => by
    simp only [Cert.check] at h
    have r := Poly.eval_of_constNegF h env
    rw [eval_substAll env subs _ hsub] at r
    have := PE.nonneg c env hs e; omega
  | subs, .split v c0 c1, h, hsub => by
    simp only [Cert.check, Bool.and_eq_true] at h
    obtain ⟨⟨hb, h0⟩, h1⟩ := h
    have := hs.bool v hb
    rcases (show env v = 0 ∨ env v = 1 by omega) with e | e
    · exact Cert.sound c env hs T _ c0 h0 (fun s m => by
        rcases List.mem_cons.1 m with rfl | m
        · exact e
        · exact hsub s m)
    · exact Cert.sound c env hs T _ c1 h1 (fun s m => by
        rcases List.mem_cons.1 m with rfl | m
        · exact e
        · exact hsub s m)

/-! ### Rounding: integer quotients from rational bounds -/

theorem le_zero_of_bound (K c q : Int) (hK : 0 < K) (hc : c < K) (h : 0 ≤ c - K * q) : q ≤ 0 := by
  rcases Int.lt_or_le 0 q with hq | hq
  · have : K * 1 ≤ K * q := Int.mul_le_mul_of_nonneg_left hq (Int.le_of_lt hK)
    omega
  · exact hq

theorem one_le_of_bound (K c q : Int) (hK : 0 < K) (hc : c < 0) (h : 0 ≤ K * q + c) : 1 ≤ q := by
  rcases Int.lt_or_le q 1 with hq | hq
  · have : K * q ≤ K * 0 := Int.mul_le_mul_of_nonneg_left (by omega) (Int.le_of_lt hK)
    omega
  · exact hq

/-! ### The context is sound on the actual table -/

theorem ctx_sound (inputs : List (BitVec 64)) (defs : List Def) (iw W : List (Nat × Nat)) (L : List Poly)
    (hlen : iw.length = inputs.length) (hin : ∀ i, i < inputs.length → WidthOK (inputs.getD i 0) (iw.getD i (64, 0)))
    (wf : WF inputs.length defs = true) (small : inputs.length + defs.length ≤ BIG)
    (hW : widthTable iw defs = W)
    (hL : ∀ t, t < inputs.length + defs.length →
      (((evalDefs inputs defs).getD t 0).toNat : Int) = Poly.eval (envOf inputs.length defs (evalDefs inputs defs)) (L.getD t []))
    (hLlen : L.length = inputs.length + defs.length) :
    Ctx.Sound ⟨inputs.length, defs, W, L⟩ (envOf inputs.length defs (evalDefs inputs defs)) := by
  have widths := width_sound inputs defs iw hlen hin wf
  rw [hW] at widths
  have outside : ∀ t, ¬ t < inputs.length + defs.length → L.getD t [] = [] := by
    intro t ht
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : L.length ≤ t)]
  have boolv : ∀ t, Ctx.isBool ⟨inputs.length, defs, W, L⟩ t = true →
      t < inputs.length + defs.length ∧ ((evalDefs inputs defs).getD t 0).toNat ≤ 1 := by
    intro t h
    simp only [Ctx.isBool, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hn, hd⟩ := h
    cases hdk : defs[t - inputs.length]? with
    | none => simp [hdk] at hd
    | some d =>
      simp only [hdk] at hd
      have hk : t - inputs.length < defs.length := by
        rcases Nat.lt_or_ge (t - inputs.length) defs.length with h | h
        · exact h
        · simp [List.getElem?_eq_none h] at hdk
      refine ⟨by omega, ?_⟩
      have e : t = inputs.length + (t - inputs.length) := by omega
      rw [e, vals_entry inputs defs wf _ d hdk]
      exact boolDef_le d hd _ (by simp)
  refine ⟨?_, ?_⟩
  · intro a
    cases a with
    | val t =>
      simp only [Atom.poly]
      by_cases ht : t < inputs.length + defs.length
      · rw [← hL t ht]; omega
      · rw [outside t ht]; simp [Poly.eval_nil]
    | wid t =>
      simp only [Atom.poly]
      rw [Poly.eval_sub, Poly.eval_const]
      by_cases ht : t < inputs.length + defs.length
      · rw [← hL t ht]
        have := (widths t ht).1
        have : (((evalDefs inputs defs).getD t 0).toNat : Int) < (2 : Int) ^ (W.getD t (64, 0)).1 := by
          exact_mod_cast this
        omega
      · rw [outside t ht, Poly.eval_nil]
        have : (0 : Int) < 2 ^ (W.getD t (64, 0)).1 := Int.pow_pos (by decide)
        omega
    | bit t =>
      simp only [Atom.poly]
      split
      · next h =>
        obtain ⟨ht, hb⟩ := boolv t h
        rw [Poly.eval_sub, Poly.eval_const, ← hL t ht]; omega
      · simp [Poly.eval_nil]
    | quot t =>
      simp only [Atom.poly, Poly.eval_var, envOf]
      split
      · omega
      · split <;> omega
  · intro t h
    obtain ⟨ht, hb⟩ := boolv t h
    have : envOf inputs.length defs (evalDefs inputs defs) t = (((evalDefs inputs defs).getD t 0).toNat : Int) :=
      env_low inputs defs t (by omega)
    rw [this]; omega

#print axioms Cert.sound
#print axioms ctx_sound
end TranslateValue
