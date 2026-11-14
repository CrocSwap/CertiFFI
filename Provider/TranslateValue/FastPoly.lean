import TranslateValue.Poly

/-! A merge-sort normal form for polynomials (O(k log k) monomial comparisons), for kernel checks on tables of
hundreds of terms. Soundness never depends on the comparison: every step preserves `Poly.eval`; the order only
decides whether equal monomials meet and cancel. -/

set_option autoImplicit false
namespace TranslateValue

/-- Lexicographic comparison of (sorted) monomials. -/
def Mono.cmp : Mono → Mono → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: m, b :: m' => match compare a b with
    | .eq => Mono.cmp m m'
    | o => o

/-- Merge two term lists, combining equal monomials (fuel bounds the recursion; leftovers are appended). -/
def Poly.mergeF : Nat → Poly → Poly → Poly
  | 0, p, q => p ++ q
  | _ + 1, [], q => q
  | _ + 1, p, [] => p
  | f + 1, t :: p, u :: q => match Mono.cmp t.2 u.2 with
    | .lt => t :: Poly.mergeF f p (u :: q)
    | .gt => u :: Poly.mergeF f (t :: p) q
    | .eq => (t.1 + u.1, t.2) :: Poly.mergeF f p q

theorem Poly.eval_append (env : Nat → Int) (p q : Poly) : Poly.eval env (p ++ q) = Poly.eval env p + Poly.eval env q := by
  have := Poly.eval_add env p q; simpa [Poly.add] using this

theorem Poly.eval_mergeF (env : Nat → Int) : ∀ (f : Nat) (p q : Poly),
    Poly.eval env (Poly.mergeF f p q) = Poly.eval env p + Poly.eval env q
  | 0, p, q => by simp only [Poly.mergeF]; exact Poly.eval_append env p q
  | _ + 1, [], q => by simp [Poly.mergeF, Poly.eval_nil]
  | _ + 1, _ :: _, [] => by simp [Poly.mergeF, Poly.eval_nil]
  | f + 1, t :: p, u :: q => by
    simp only [Poly.mergeF]
    split
    · simp only [Poly.eval_cons, Poly.eval_mergeF env f]; omega
    · simp only [Poly.eval_cons, Poly.eval_mergeF env f]; omega
    · next h =>
      have e : Mono.eval env t.2 = Mono.eval env u.2 := by
        have : t.2 = u.2 := by
          clear p q f
          obtain ⟨_, m⟩ := t; obtain ⟨_, m'⟩ := u
          simp only at h ⊢
          induction m generalizing m' with
          | nil => cases m' <;> simp_all [Mono.cmp]
          | cons a m ih =>
            cases m' with
            | nil => simp [Mono.cmp] at h
            | cons b m' =>
              simp only [Mono.cmp] at h
              split at h
              · next hc => rw [Nat.compare_eq_eq] at hc; rw [hc, ih m' h]
              · simp_all
        rw [this]
      simp only [Poly.eval_cons, Poly.eval_mergeF env f, e, Int.add_mul]; omega

/-- One bottom-up round: merge adjacent runs. -/
def Poly.mergePairs : List Poly → List Poly
  | p :: q :: rs => Poly.mergeF (p.length + q.length) p q :: Poly.mergePairs rs
  | rs => rs

def Poly.evalRuns (env : Nat → Int) (rs : List Poly) : Int := (rs.map (Poly.eval env)).sum

theorem Poly.evalRuns_mergePairs (env : Nat → Int) : ∀ rs : List Poly,
    Poly.evalRuns env (Poly.mergePairs rs) = Poly.evalRuns env rs
  | p :: q :: rs => by
    simp only [Poly.mergePairs, Poly.evalRuns, List.map_cons, List.sum_cons] at *
    have := Poly.evalRuns_mergePairs env rs
    simp only [Poly.evalRuns] at this
    rw [this, Poly.eval_mergeF]; omega
  | [] => rfl
  | [_] => rfl

def Poly.mergeAll : Nat → List Poly → Poly
  | _, [] => []
  | _, [p] => p
  | 0, rs => rs.flatten
  | f + 1, rs => Poly.mergeAll f (Poly.mergePairs rs)

theorem Poly.eval_flatten (env : Nat → Int) : ∀ rs : List Poly, Poly.eval env rs.flatten = Poly.evalRuns env rs
  | [] => rfl
  | p :: rs => by
    simp only [List.flatten_cons, Poly.evalRuns, List.map_cons, List.sum_cons]
    rw [Poly.eval_append, Poly.eval_flatten env rs]; rfl

theorem Poly.eval_mergeAll (env : Nat → Int) : ∀ (f : Nat) (rs : List Poly),
    Poly.eval env (Poly.mergeAll f rs) = Poly.evalRuns env rs
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | _, [p] => by simp [Poly.mergeAll, Poly.evalRuns]
  | 0, _ :: _ :: _ => by simp only [Poly.mergeAll]; exact Poly.eval_flatten env _
  | f + 1, _ :: _ :: _ => by
    simp only [Poly.mergeAll]; rw [Poly.eval_mergeAll env f, Poly.evalRuns_mergePairs]

/-- Fast normal form: sort each monomial, merge-sort the terms combining like monomials, drop zeros. -/
def Poly.normF (p : Poly) : Poly :=
  (Poly.mergeAll p.length (p.map fun t => [(t.1, Mono.sort t.2)])).filter (fun t => t.1 != 0)

theorem Poly.eval_normF (env : Nat → Int) (p : Poly) : Poly.eval env (Poly.normF p) = Poly.eval env p := by
  unfold Poly.normF
  have hf : ∀ q : Poly, Poly.eval env (q.filter (fun t => t.1 != 0)) = Poly.eval env q := by
    intro q
    induction q with
    | nil => rfl
    | cons t q ih =>
      by_cases h : t.1 = 0
      · rw [List.filter_cons_of_neg (by simp [h]), ih, Poly.eval_cons, h]; simp
      · rw [List.filter_cons_of_pos (by simp [h]), Poly.eval_cons, Poly.eval_cons, ih]
  rw [hf, Poly.eval_mergeAll]
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [List.map_cons, Poly.evalRuns, List.sum_cons] at *
    rw [ih, Poly.eval_cons, Poly.eval_cons, Poly.eval_nil, Mono.eval_sort, Int.add_zero]

def Poly.isZeroF (p : Poly) : Bool := (Poly.normF p).isEmpty

theorem Poly.eval_of_isZeroF {p : Poly} (h : Poly.isZeroF p = true) (env : Nat → Int) : Poly.eval env p = 0 := by
  rw [← Poly.eval_normF]; unfold Poly.isZeroF at h
  rw [List.isEmpty_iff.1 h]; rfl

/-- p and q agree as polynomials. -/
def Poly.eqF (p q : Poly) : Bool := Poly.isZeroF (Poly.sub p q)

theorem Poly.eval_of_eqF {p q : Poly} (h : Poly.eqF p q = true) (env : Nat → Int) :
    Poly.eval env p = Poly.eval env q := by
  have := Poly.eval_of_isZeroF h env; rw [Poly.eval_sub] at this; omega

/-- The normal form is a single constant term ≥ 0 (or empty). -/
def Poly.constNonnegF (p : Poly) : Bool :=
  match Poly.normF p with
  | [] => true
  | [(c, [])] => decide (0 ≤ c)
  | _ => false

theorem Poly.eval_of_constNonnegF {p : Poly} (h : Poly.constNonnegF p = true) (env : Nat → Int) :
    0 ≤ Poly.eval env p := by
  rw [← Poly.eval_normF]; unfold Poly.constNonnegF at h
  split at h
  · next he => rw [he]; exact Int.le_refl 0
  · next c he => rw [he]; simp [Poly.eval_cons, Poly.eval_nil, Mono.eval_nil]; exact of_decide_eq_true h
  · cases h

/-- The normal form is a single constant term < 0. -/
def Poly.constNegF (p : Poly) : Bool :=
  match Poly.normF p with
  | [(c, [])] => decide (c < 0)
  | _ => false

theorem Poly.eval_of_constNegF {p : Poly} (h : Poly.constNegF p = true) (env : Nat → Int) :
    Poly.eval env p < 0 := by
  rw [← Poly.eval_normF]; unfold Poly.constNegF at h
  split at h
  · next c he => rw [he]; simp [Poly.eval_cons, Poly.eval_nil, Mono.eval_nil]; exact of_decide_eq_true h
  · cases h

theorem fast_sanity : Poly.isZeroF (Poly.sub (Poly.mul (Poly.add (Poly.var 1) (Poly.var 2)) (Poly.add (Poly.var 1) (Poly.var 2)))
    [(1, [1, 1]), (2, [2, 1]), (1, [2, 2])]) = true := by decide +kernel

#print axioms Poly.eval_normF
#print axioms Poly.eval_of_constNegF
end TranslateValue
