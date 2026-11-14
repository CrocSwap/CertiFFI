-- (CT2): ArmCertPipe.Physical.AgreesAt (legacy StepV prefix, Runtime14) variants of the pair lemma, and the extend
-- prefix lemma (an input slot keeps its value in the extended table), for "returned unchanged" registers.
import CT2Core.Pair
import ArmCertPipe.PhysicalPrefix
set_option autoImplicit false
namespace CT2Core
open ArmCertValue HeapV2StepCerts.RegBind

theorem agreesAt_pairP {view1 view2 : Physical.BytePA} {regions : List Region} {σ0 : Sym}
    {v1 v2 : List (BitVec 64)} {plan : List StepV} {k : Nat} {s1 s2 : St}
    (h1 : ArmCertPipe.Physical.AgreesAt view1 regions σ0 v1 plan k s1)
    (h2 : ArmCertPipe.Physical.AgreesAt view2 regions σ0 v2 plan k s2)
    (hl : v1.length = v2.length) :
    ∃ ds σ, compileRun regions σ0 v1.length (plan.take k) = some (ds, σ) ∧
      Physical.Agrees view1 (extend v1 ds) σ s1 ∧ Physical.Agrees view2 (extend v2 ds) σ s2 := by
  obtain ⟨d1, r1, c1, a1, _⟩ := h1
  obtain ⟨d2, r2, c2, a2, _⟩ := h2
  rw [← hl, c1] at c2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj c2)
  exact ⟨d1, r1, c1, a1, a2⟩

/-- extend only appends: an input slot keeps its value. -/
theorem extend_getD_lt (defs : List Def) : ∀ (v : List (BitVec 64)) (i : Nat), i < v.length →
    (extend v defs).getD i 0 = v.getD i 0 := by
  induction defs with
  | nil => intro v i _; simp [extend]
  | cons d rest ih =>
    intro v i hi
    have h := ih (v ++ [d.eval v]) i (by simp; omega)
    simp only [extend, List.foldl_cons] at h ⊢
    rw [h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-- A register whose final table id is its own entry id (< inputs length) is returned unchanged. -/
theorem reg_unchanged {view : Physical.BytePA} {v : List (BitVec 64)} {ds : List Def} {σ0 σ : Sym} {s0 s : St}
    (a0 : Physical.Agrees view v σ0 s0) (a : Physical.Agrees view (extend v ds) σ s) (r : Reg) (i : Nat)
    (h0 : σ0.regs r = some i) (h : σ.regs r = some i) (hi : i < v.length) : regVal s r = regVal s0 r := by
  rw [a.1 r i h, a0.1 r i h0, extend_getD_lt ds v i hi]

#print axioms agreesAt_pairP
#print axioms extend_getD_lt
#print axioms reg_unchanged
end CT2Core
