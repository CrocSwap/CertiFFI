-- (CT2 residue generator,): public-mask propagation over the ArmCertValue SSA value table.
-- If two input tables agree on every public slot, the extended tables (same defs) agree on every slot the
-- mask marks public. The mask is computable, so each card decides it.
import ArmCertValue.Core
set_option autoImplicit false
namespace CT2Core
open ArmCertValue

/-- An argument is public under mask p: an immediate, or a table id marked public. -/
def argPub (p : List Bool) : Arg → Bool
  | .id n => p.getD n false
  | .imm _ => true

/-- Extend the mask in step with `extend`: a definition is public iff all its arguments are. -/
def pubExtend (p : List Bool) (defs : List Def) : List Bool :=
  defs.foldl (fun p d => p ++ [d.args.all (argPub p)]) p

/-- Two tables agree on the public slots of mask p (and have p's length). -/
def AgreeOn (p : List Bool) (v1 v2 : List (BitVec 64)) : Prop :=
  v1.length = p.length ∧ v2.length = p.length ∧ ∀ i, p.getD i false = true → v1.getD i 0 = v2.getD i 0

theorem argEval_eq {p : List Bool} {v1 v2 : List (BitVec 64)} (h : AgreeOn p v1 v2) (a : Arg)
    (ha : argPub p a = true) : a.eval v1 = a.eval v2 := by
  cases a with
  | id n => exact h.2.2 n ha
  | imm c => rfl

theorem defEval_eq {p : List Bool} {v1 v2 : List (BitVec 64)} (h : AgreeOn p v1 v2) (d : Def)
    (hd : d.args.all (argPub p) = true) : d.eval v1 = d.eval v2 := by
  unfold Def.eval
  congr 1
  apply List.map_congr_left
  intro a ha
  exact argEval_eq h a (List.all_eq_true.mp hd a ha)

theorem agreeOn_snoc {p : List Bool} {v1 v2 : List (BitVec 64)} (h : AgreeOn p v1 v2) (d : Def) :
    AgreeOn (p ++ [d.args.all (argPub p)]) (v1 ++ [d.eval v1]) (v2 ++ [d.eval v2]) := by
  obtain ⟨l1, l2, hp⟩ := h
  refine ⟨by simp [l1], by simp [l2], ?_⟩
  intro i hi
  by_cases hlt : i < p.length
  · have hi' : p.getD i false = true := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hi
      rwa [List.getD_eq_getElem?_getD]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
    have := hp i hi'
    rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at this
  · by_cases heq : i = p.length
    · subst heq
      have hd : d.args.all (argPub p) = true := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)] at hi
        simpa using hi
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
      simp only [l1, l2, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      exact defEval_eq ⟨l1, l2, hp⟩ d hd
    · exfalso
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
      simp at hi

/-- **Core CT2 lemma.** Agreement on the public inputs propagates through the SSA extension. -/
theorem agreeOn_extend (defs : List Def) : ∀ (p : List Bool) (v1 v2 : List (BitVec 64)),
    AgreeOn p v1 v2 → AgreeOn (pubExtend p defs) (extend v1 defs) (extend v2 defs) := by
  induction defs with
  | nil => intro p v1 v2 h; simpa [pubExtend, extend] using h
  | cons d rest ih =>
    intro p v1 v2 h
    have := ih _ _ _ (agreeOn_snoc h d)
    simpa [pubExtend, extend, List.foldl_cons] using this

/-- extend only appends: an input slot keeps its value. -/
theorem extend_getD_lt' (defs : List Def) : ∀ (v : List (BitVec 64)) (i : Nat), i < v.length →
    (extend v defs).getD i 0 = v.getD i 0 := by
  induction defs with
  | nil => intro v i _; simp [extend]
  | cons d rest ih =>
    intro v i hi
    have h := ih (v ++ [d.eval v]) i (by simp; omega)
    simp only [extend, List.foldl_cons] at h ⊢
    rw [h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-- The MRS DIT image of a DIT bit: bit 24 = the bit, all other bits RES0 (= zeroExtend b <<< 24). -/
def ditImage (b : BitVec 1) : BitVec 64 := ((0#39).append b).append 0#24

#print axioms agreeOn_extend
end CT2Core
