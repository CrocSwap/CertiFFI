/-! ArmCert value layer, normalizer: integer polynomials over variable indices, with a
kernel-decidable zero test that is SOUND for evaluation (if `isZero p` then `eval env p = 0` for every `env`).
Only soundness is proved; completeness (that the check succeeds) is the generator's job. Pure Lean core, no
Mathlib; no bv_decide/native_decide. -/

set_option autoImplicit false
namespace TranslateValue

/-- A monomial: a multiset of variable indices (as a list). -/
abbrev Mono := List Nat

def Mono.eval (env : Nat → Int) (m : Mono) : Int := m.foldr (fun v acc => env v * acc) 1

theorem Mono.eval_nil (env : Nat → Int) : Mono.eval env [] = 1 := rfl

theorem Mono.eval_cons (env : Nat → Int) (v : Nat) (m : Mono) : Mono.eval env (v :: m) = env v * Mono.eval env m := rfl

theorem Mono.eval_append (env : Nat → Int) (m n : Mono) : Mono.eval env (m ++ n) = Mono.eval env m * Mono.eval env n := by
  induction m with
  | nil => simp [Mono.eval_nil]
  | cons v m ih => rw [List.cons_append, Mono.eval_cons, Mono.eval_cons, ih, Int.mul_assoc]

/-- Insert into a sorted monomial. -/
def Mono.insert (v : Nat) : Mono → Mono
  | [] => [v]
  | a :: m => if v ≤ a then v :: a :: m else a :: Mono.insert v m

theorem Mono.eval_insert (env : Nat → Int) (v : Nat) (m : Mono) :
    Mono.eval env (Mono.insert v m) = env v * Mono.eval env m := by
  induction m with
  | nil => rfl
  | cons a m ih =>
    unfold Mono.insert
    split
    · rfl
    · rw [Mono.eval_cons, ih, Mono.eval_cons, Int.mul_left_comm]

/-- Canonical (sorted) form of a monomial. -/
def Mono.sort (m : Mono) : Mono := m.foldr Mono.insert []

theorem Mono.eval_sort (env : Nat → Int) (m : Mono) : Mono.eval env (Mono.sort m) = Mono.eval env m := by
  induction m with
  | nil => rfl
  | cons v m ih => simp only [Mono.sort, List.foldr_cons] at *; rw [Mono.eval_insert, ih, Mono.eval_cons]

/-- A polynomial: a list of (coefficient, monomial) terms. -/
abbrev Poly := List (Int × Mono)

def Poly.eval (env : Nat → Int) (p : Poly) : Int := p.foldr (fun t acc => t.1 * Mono.eval env t.2 + acc) 0

theorem Poly.eval_nil (env : Nat → Int) : Poly.eval env [] = 0 := rfl

theorem Poly.eval_cons (env : Nat → Int) (t : Int × Mono) (p : Poly) :
    Poly.eval env (t :: p) = t.1 * Mono.eval env t.2 + Poly.eval env p := rfl

def Poly.const (c : Int) : Poly := [(c, [])]
def Poly.var (v : Nat) : Poly := [(1, [v])]
def Poly.add (p q : Poly) : Poly := p ++ q
def Poly.scale (c : Int) (p : Poly) : Poly := p.map fun t => (c * t.1, t.2)
def Poly.neg (p : Poly) : Poly := Poly.scale (-1) p
def Poly.sub (p q : Poly) : Poly := Poly.add p (Poly.neg q)
def Poly.mulTerm (t : Int × Mono) (q : Poly) : Poly := q.map fun u => (t.1 * u.1, t.2 ++ u.2)
def Poly.mul (p q : Poly) : Poly := p.flatMap fun t => Poly.mulTerm t q

theorem Poly.eval_const (env : Nat → Int) (c : Int) : Poly.eval env (Poly.const c) = c := by
  simp [Poly.eval, Poly.const, Mono.eval]

theorem Poly.eval_var (env : Nat → Int) (v : Nat) : Poly.eval env (Poly.var v) = env v := by
  simp [Poly.eval, Poly.var, Mono.eval]

theorem Poly.eval_add (env : Nat → Int) (p q : Poly) : Poly.eval env (Poly.add p q) = Poly.eval env p + Poly.eval env q := by
  induction p with
  | nil => simp [Poly.add, Poly.eval_nil]
  | cons t p ih =>
    simp only [Poly.add, List.cons_append] at *
    rw [Poly.eval_cons, ih, Poly.eval_cons, Int.add_assoc]

theorem Poly.eval_scale (env : Nat → Int) (c : Int) (p : Poly) : Poly.eval env (Poly.scale c p) = c * Poly.eval env p := by
  induction p with
  | nil => simp [Poly.scale, Poly.eval_nil]
  | cons t p ih =>
    simp only [Poly.scale, List.map_cons] at *
    rw [Poly.eval_cons, ih, Poly.eval_cons, Int.mul_add, Int.mul_assoc]

theorem Poly.eval_neg (env : Nat → Int) (p : Poly) : Poly.eval env (Poly.neg p) = - Poly.eval env p := by
  rw [Poly.neg, Poly.eval_scale, Int.neg_one_mul]

theorem Poly.eval_sub (env : Nat → Int) (p q : Poly) : Poly.eval env (Poly.sub p q) = Poly.eval env p - Poly.eval env q := by
  rw [Poly.sub, Poly.eval_add, Poly.eval_neg, Int.sub_eq_add_neg]

theorem Poly.eval_mulTerm (env : Nat → Int) (t : Int × Mono) (q : Poly) :
    Poly.eval env (Poly.mulTerm t q) = t.1 * Mono.eval env t.2 * Poly.eval env q := by
  induction q with
  | nil => simp [Poly.mulTerm, Poly.eval_nil]
  | cons u q ih =>
    simp only [Poly.mulTerm, List.map_cons] at *
    rw [Poly.eval_cons, ih, Poly.eval_cons, Mono.eval_append, Int.mul_add]
    congr 1
    simp only [Int.mul_assoc, Int.mul_left_comm]

theorem Poly.eval_mul (env : Nat → Int) (p q : Poly) : Poly.eval env (Poly.mul p q) = Poly.eval env p * Poly.eval env q := by
  induction p with
  | nil => simp [Poly.mul, Poly.eval_nil]
  | cons t p ih =>
    simp only [Poly.mul, List.flatMap_cons] at *
    have := Poly.eval_add env (Poly.mulTerm t q) (p.flatMap fun t => Poly.mulTerm t q)
    simp only [Poly.add] at this
    rw [this, ih, Poly.eval_mulTerm, Poly.eval_cons, Int.add_mul]

/-- Add a term into a list, combining it with an equal monomial if present. -/
def Poly.insertTerm (t : Int × Mono) : Poly → Poly
  | [] => [t]
  | u :: p => if t.2 = u.2 then (t.1 + u.1, u.2) :: p else u :: Poly.insertTerm t p

theorem Poly.eval_insertTerm (env : Nat → Int) (t : Int × Mono) (p : Poly) :
    Poly.eval env (Poly.insertTerm t p) = t.1 * Mono.eval env t.2 + Poly.eval env p := by
  induction p with
  | nil => rfl
  | cons u p ih =>
    unfold Poly.insertTerm
    split
    · next h => rw [Poly.eval_cons, Poly.eval_cons, h, Int.add_mul, Int.add_assoc]
    · rw [Poly.eval_cons, ih, Poly.eval_cons, Int.add_left_comm]

/-- Normal form: sorted monomials, like terms combined. -/
def Poly.normalize (p : Poly) : Poly := p.foldr (fun t acc => Poly.insertTerm (t.1, Mono.sort t.2) acc) []

theorem Poly.eval_normalize (env : Nat → Int) (p : Poly) : Poly.eval env (Poly.normalize p) = Poly.eval env p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [Poly.normalize, List.foldr_cons] at *
    rw [Poly.eval_insertTerm, Mono.eval_sort, ih, Poly.eval_cons]

/-- Zero test on the normal form: every combined coefficient is 0. -/
def Poly.isZero (p : Poly) : Bool := (Poly.normalize p).all fun t => t.1 == 0

theorem Poly.eval_of_all_zero (env : Nat → Int) (p : Poly) (h : p.all (fun t => t.1 == 0) = true) :
    Poly.eval env p = 0 := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rw [Poly.eval_cons, h.1, ih h.2]; simp

/-- Soundness of the zero test. -/
theorem Poly.eval_of_isZero {p : Poly} (h : Poly.isZero p = true) (env : Nat → Int) : Poly.eval env p = 0 := by
  rw [← Poly.eval_normalize]; exact Poly.eval_of_all_zero env _ h

/-- Sanity: (x + y)^2 = x^2 + 2xy + y^2, decided by the kernel. -/
theorem sanity_square :
    Poly.isZero (Poly.sub (Poly.mul (Poly.add (Poly.var 0) (Poly.var 1)) (Poly.add (Poly.var 0) (Poly.var 1)))
      (Poly.add (Poly.mul (Poly.var 0) (Poly.var 0))
        (Poly.add (Poly.scale 2 (Poly.mul (Poly.var 0) (Poly.var 1))) (Poly.mul (Poly.var 1) (Poly.var 1))))) = true := by
  decide +kernel

#print axioms Poly.eval_of_isZero
#print axioms sanity_square
end TranslateValue
