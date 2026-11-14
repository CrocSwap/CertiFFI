import TranslateValue.SymMain

/-! ArmCert value layer, normalizer: the generic BOUND checker.
A Farkas-style linear certificate, checked by the kernel: from per-variable bounds (0 ≤ x ≤ U_x, both used with
NONNEGATIVE constant multipliers) and known-zero polynomials (multipliers of any sign), the remainder of a
target T normalizes to a nonnegative constant, hence eval T ≥ 0. Boolean case splits are by substitution
(`Poly.subst`): checking T[b := 0] and T[b := 1] proves T when env b ∈ {0,1}. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace TranslateValue

/-! ### Substitution of a variable by a constant -/

def Mono.subst (v : Nat) (c : Int) : Mono → Int × Mono
  | [] => (1, [])
  | x :: m => let r := Mono.subst v c m; if x = v then (c * r.1, r.2) else (r.1, x :: r.2)

theorem Mono.eval_subst (env : Nat → Int) (v : Nat) (c : Int) (hv : env v = c) (m : Mono) :
    (Mono.subst v c m).1 * Mono.eval env (Mono.subst v c m).2 = Mono.eval env m := by
  induction m with
  | nil => simp [Mono.subst, Mono.eval_nil]
  | cons x m ih =>
    simp only [Mono.subst]
    split
    · next h => subst h; rw [Mono.eval_cons, ← ih, hv]; simp only [Int.mul_assoc]
    · rw [Mono.eval_cons, Mono.eval_cons, ← ih, Int.mul_left_comm]

def Poly.subst (v : Nat) (c : Int) (p : Poly) : Poly :=
  p.map fun t => let r := Mono.subst v c t.2; (t.1 * r.1, r.2)

theorem Poly.eval_subst (env : Nat → Int) (v : Nat) (c : Int) (hv : env v = c) (p : Poly) :
    Poly.eval env (Poly.subst v c p) = Poly.eval env p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [Poly.subst, List.map_cons] at *
    rw [Poly.eval_cons, ih, Poly.eval_cons, Int.mul_assoc, Mono.eval_subst env v c hv]

/-! ### Linear certificate -/

/-- A certificate: lower-bound multipliers (x ≥ 0), upper-bound multipliers (U − x ≥ 0), and equation
    multipliers (E = 0), with E given as polynomials. -/
structure LinCert where
  lows : List (Nat × Int)
  highs : List (Nat × Int × Int)          -- (x, U, λ): λ·(U − x)
  eqs : List (Int × Poly)                 -- (μ, E): μ·E

def LinCert.combo (c : LinCert) : Poly :=
  Poly.add (c.lows.flatMap fun l => Poly.scale l.2 (Poly.var l.1))
    (Poly.add (c.highs.flatMap fun h => Poly.scale h.2.2 (Poly.sub (Poly.const h.2.1) (Poly.var h.1)))
      (c.eqs.flatMap fun e => Poly.scale e.1 e.2))

/-- The normal form is a single constant term ≥ 0 (or empty). -/
def Poly.constNonneg (p : Poly) : Bool :=
  (Poly.normalize p).all fun t => t.2 = [] && decide (0 ≤ t.1) || t.1 == 0

def LinCert.check (T : Poly) (c : LinCert) : Bool :=
  c.lows.all (fun l => decide (0 ≤ l.2)) && c.highs.all (fun h => decide (0 ≤ h.2.2)) &&
    Poly.constNonneg (Poly.sub T c.combo)

theorem eval_flatMap (env : Nat → Int) {α : Type} (xs : List α) (f : α → Poly) :
    Poly.eval env (xs.flatMap f) = (xs.map fun x => Poly.eval env (f x)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
    have := Poly.eval_add env (f x) (xs.flatMap f)
    simp only [Poly.add] at this
    rw [this, ih]

theorem sum_zero {α : Type} (xs : List α) (g : α → Int) (h : ∀ x ∈ xs, g x = 0) : (xs.map g).sum = 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h x List.mem_cons_self, ih (fun y m => h y (List.mem_cons_of_mem x m))]; simp

theorem sum_nonneg {α : Type} (xs : List α) (g : α → Int) (h : ∀ x ∈ xs, 0 ≤ g x) : 0 ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    have a := h x List.mem_cons_self
    have b := ih (fun y m => h y (List.mem_cons_of_mem x m))
    omega

theorem eval_allConst (env : Nat → Int) (q : Poly)
    (h : q.all (fun t => t.2 = [] && decide (0 ≤ t.1) || t.1 == 0) = true) : 0 ≤ Poly.eval env q := by
  induction q with
  | nil => simp [Poly.eval_nil]
  | cons t q ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [Poly.eval_cons]
    have rest := ih h.2
    have hd := h.1
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hd
    rcases hd with ⟨hm, hc⟩ | hz
    · have : t.2 = [] := by simpa using hm
      rw [this, Mono.eval_nil, Int.mul_one]; omega
    · rw [hz, Int.zero_mul]; omega

theorem eval_constNonneg (env : Nat → Int) (p : Poly) (h : Poly.constNonneg p = true) : 0 ≤ Poly.eval env p := by
  rw [← Poly.eval_normalize]; exact eval_allConst env _ h

/-- Soundness: if the certificate checks and env satisfies the bounds and the equations, then eval T ≥ 0. -/
theorem LinCert.sound (env : Nat → Int) (T : Poly) (c : LinCert) (h : c.check T = true)
    (lo : ∀ l ∈ c.lows, 0 ≤ env l.1) (hi : ∀ x ∈ c.highs, env x.1 ≤ x.2.1)
    (eq : ∀ e ∈ c.eqs, Poly.eval env e.2 = 0) : 0 ≤ Poly.eval env T := by
  simp only [LinCert.check, Bool.and_eq_true] at h
  obtain ⟨⟨hl, hh⟩, hr⟩ := h
  have r := eval_constNonneg env _ hr
  rw [Poly.eval_sub] at r
  have c1 : 0 ≤ Poly.eval env c.combo := by
    simp only [LinCert.combo]
    rw [Poly.eval_add, Poly.eval_add, eval_flatMap, eval_flatMap, eval_flatMap]
    have a := sum_nonneg c.lows (fun l => Poly.eval env (Poly.scale l.2 (Poly.var l.1))) (by
      intro l m; rw [Poly.eval_scale, Poly.eval_var]
      exact Int.mul_nonneg (of_decide_eq_true (List.all_eq_true.1 hl l m)) (lo l m))
    have b := sum_nonneg c.highs (fun x => Poly.eval env (Poly.scale x.2.2 (Poly.sub (Poly.const x.2.1) (Poly.var x.1)))) (by
      intro x m; rw [Poly.eval_scale, Poly.eval_sub, Poly.eval_const, Poly.eval_var]
      exact Int.mul_nonneg (of_decide_eq_true (List.all_eq_true.1 hh x m)) (by have := hi x m; omega))
    have e : (c.eqs.map fun e => Poly.eval env (Poly.scale e.1 e.2)).sum = 0 := by
      have : ∀ x ∈ c.eqs, Poly.eval env (Poly.scale x.1 x.2) = 0 := by
        intro x m; rw [Poly.eval_scale, eq x m, Int.mul_zero]
      exact sum_zero _ _ this
    omega
  omega

#print axioms Poly.eval_subst
#print axioms LinCert.sound
end TranslateValue
