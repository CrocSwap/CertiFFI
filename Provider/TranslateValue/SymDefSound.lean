import TranslateValue.SymSound

/-! Per-entry soundness of `symDef`, over abstract hypotheses about the environment. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TranslateValue
open ArmCertValue

theorem symDef_sound (n : Nat) (defs : List Def) (tbl : List Poly) (d : Def) (env : Nat → Int)
    (vals : List (BitVec 64))
    (hP : ∀ a ∈ d.args, Poly.eval env (argPoly tbl a) = ((Arg.eval vals a).toNat : Int))
    (hv : vals.getD tbl.length 0 = d.op.eval (d.args.map (Arg.eval vals)))
    (hself : env tbl.length = ((vals.getD tbl.length 0).toNat : Int))
    (hq : env (BIG + tbl.length) = (quot vals d : Int))
    (hpartner : ∀ o args j, findDef o args defs 0 = some j →
      env (n + j) = (((o.eval (args.map (Arg.eval vals))).toNat : Nat) : Int))
    (hbool : ∀ c, boolId n defs c = true → (Arg.eval vals c).toNat ≤ 1) :
    Poly.eval env (symDef n defs tbl d) = ((vals.getD tbl.length 0).toNat : Int) := by
  obtain ⟨op, args⟩ := d
  have fallback : Poly.eval env (Poly.var tbl.length) = ((vals.getD tbl.length 0).toNat : Int) := by
    rw [Poly.eval_var, hself]
  cases op <;> simp only [symDef] <;> (try exact fallback)
  · -- const
    rw [Poly.eval_const, hv]; simp only [List.map]; rw [const_nat]
  · -- add
    split
    · next a b =>
      have ha := hP a (by simp); have hb := hP b (by simp)
      have key := add_nat (Arg.eval vals a) (Arg.eval vals b)
      have e : Op.eval .add [Arg.eval vals a, Arg.eval vals b] = Arg.eval vals a + Arg.eval vals b := rfl
      simp only [List.map] at hv
      rw [Poly.eval_sub, Poly.eval_add, Poly.eval_scale, Poly.eval_var, ha, hb, hq, hv, e]
      simp only [quot, List.map]
      omega
    · exact fallback
  · -- sub
    split
    · next a b =>
      have ha := hP a (by simp); have hb := hP b (by simp)
      have key := sub_nat (Arg.eval vals a) (Arg.eval vals b)
      have e : Op.eval .sub [Arg.eval vals a, Arg.eval vals b] = Arg.eval vals a - Arg.eval vals b := rfl
      simp only [List.map] at hv
      rw [Poly.eval_add, Poly.eval_sub, Poly.eval_scale, Poly.eval_var, ha, hb, hq, hv, e]
      simp only [quot]
      split <;> split at key <;> omega
    · exact fallback
  · -- mul
    split
    · next a b =>
      have ha := hP a (by simp); have hb := hP b (by simp)
      have key := mul_nat (Arg.eval vals a) (Arg.eval vals b)
      have e : Op.eval .mul [Arg.eval vals a, Arg.eval vals b] = Arg.eval vals a * Arg.eval vals b := rfl
      simp only [List.map] at hv
      rw [Poly.eval_sub, Poly.eval_mul, Poly.eval_scale, ha, hb, hv, e, ← Int.natCast_mul]
      rcases hj : findDef .umulh [a, b] defs 0 with _ | j
      · simp only [hj]; rw [Poly.eval_var, hq]; simp only [quot]
        generalize (Arg.eval vals a).toNat * (Arg.eval vals b).toNat = m at key ⊢; omega
      · simp only [hj]; rw [Poly.eval_var, hpartner _ _ j hj]; simp only [List.map]; rw [umulh_nat]
        generalize (Arg.eval vals a).toNat * (Arg.eval vals b).toNat = m at key ⊢; omega
    · exact fallback
  · -- add3
    split
    · next a b c =>
      have ha := hP a (by simp); have hb := hP b (by simp); have hc := hP c (by simp)
      have key := add3_nat (Arg.eval vals a) (Arg.eval vals b) (Arg.eval vals c)
      have e : Op.eval .add3 [Arg.eval vals a, Arg.eval vals b, Arg.eval vals c] =
          Arg.eval vals a + Arg.eval vals b + Arg.eval vals c := rfl
      simp only [List.map] at hv
      rw [Poly.eval_sub, Poly.eval_add, Poly.eval_add, Poly.eval_scale, ha, hb, hc, hv, e]
      split
      · next hcb =>
        rcases hj : findDef .carry3 [a, b, c] defs 0 with _ | j
        · simp only [hj]; rw [Poly.eval_var, hq]; simp only [quot]; omega
        · simp only [hj]; rw [Poly.eval_var, hpartner _ _ j hj]; simp only [List.map]
          rw [carry3_nat _ _ _ (hbool c hcb)]; omega
      · rw [Poly.eval_var, hq]; simp only [quot]; omega
    · exact fallback
  · -- not
    split
    · next a =>
      have ha := hP a (by simp)
      have key := not_nat (Arg.eval vals a)
      have e : Op.eval .not [Arg.eval vals a] = ~~~(Arg.eval vals a) := rfl
      simp only [List.map] at hv
      rw [Poly.eval_sub, Poly.eval_const, ha, hv, e]
      simp only [pow64] at key ⊢; omega
    · exact fallback
  · -- lsl
    rename_i k
    split
    · next a =>
      have ha := hP a (by simp)
      have key := lsl_nat (Arg.eval vals a) k
      have e : Op.eval (.lsl k) [Arg.eval vals a] = Arg.eval vals a <<< k := rfl
      simp only [List.map] at hv
      rw [Poly.eval_sub, Poly.eval_scale, Poly.eval_scale, Poly.eval_var, ha, hq, hv, e]
      simp only [quot]
      have hm : ((2 : Int) ^ k) * ((Arg.eval vals a).toNat : Int) = (((Arg.eval vals a).toNat * 2 ^ k : Nat) : Int) := by
        rw [Int.natCast_mul, Int.natCast_pow, Int.mul_comm]; rfl
      rw [hm]
      generalize (Arg.eval vals a).toNat * 2 ^ k = m at key ⊢; omega
    · exact fallback
  · -- csel
    split
    · next w a b =>
      split
      · next hwb =>
        have hw := hP w (by simp); have ha := hP a (by simp); have hb := hP b (by simp)
        simp only [List.map] at hv
        rw [Poly.eval_add, Poly.eval_mul, Poly.eval_mul, Poly.eval_sub, Poly.eval_const, hw, ha, hb, hv,
          csel_nat _ _ _ (hbool w hwb)]
      · exact fallback
    · exact fallback

#print axioms symDef_sound
end TranslateValue
