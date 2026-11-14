import TranslateValue.SymMain

/-! End-to-end demo of the normalizer: a 64×64 → 128-bit product as SSA (mul, umulh), with its value identity
proved by `sym_sound` + one kernel-decided certificate check. -/

set_option autoImplicit false
namespace TranslateValue
open ArmCertValue

def mulDefs : List Def := [⟨.mul, [.id 0, .id 1]⟩, ⟨.umulh, [.id 0, .id 1]⟩]

theorem input_val (inputs : List (BitVec 64)) (defs : List Def) (i : Nat) (hi : i < inputs.length) :
    (evalDefs inputs defs).getD i 0 = inputs.getD i 0 := by
  unfold evalDefs extend; exact foldlApp_prefix _ _ _ _ _ hi

theorem demo_mul (x y : BitVec 64) :
    ((evalDefs [x, y] mulDefs).getD 2 0).toNat + pow64 * ((evalDefs [x, y] mulDefs).getD 3 0).toNat = x.toNat * y.toNat := by
  have wf : WF [x, y].length mulDefs = true := by simp only [List.length_cons, List.length_nil]; decide
  have small : [x, y].length + mulDefs.length ≤ BIG := by simp only [List.length_cons, List.length_nil]; decide
  have h2 := sym_sound [x, y] mulDefs wf small 2 (by simp only [List.length_cons, List.length_nil]; decide)
  have h3 := sym_sound [x, y] mulDefs wf small 3 (by simp only [List.length_cons, List.length_nil]; decide)
  have c := certified_eq [x, y] mulDefs
    (Poly.add ((symTable [x, y].length mulDefs).getD 2 (Poly.var 2))
      (Poly.scale pow64 ((symTable [x, y].length mulDefs).getD 3 (Poly.var 3))))
    (Poly.mul (Poly.var 0) (Poly.var 1)) (by simp only [List.length_cons, List.length_nil]; decide +kernel)
  rw [Poly.eval_add, Poly.eval_scale, ← h2, ← h3, Poly.eval_mul, Poly.eval_var, Poly.eval_var,
    env_low _ _ 0 (by decide), env_low _ _ 1 (by decide), input_val _ _ 0 (by simp), input_val _ _ 1 (by simp)] at c
  simp only [List.getD_cons_zero, List.getD_cons_succ] at c
  have : ((x.toNat * y.toNat : Nat) : Int) = (x.toNat : Int) * (y.toNat : Int) := Int.natCast_mul _ _
  generalize x.toNat * y.toNat = m at this ⊢
  generalize (x.toNat : Int) * (y.toNat : Int) = mi at this c
  simp only [pow64] at c ⊢
  omega

#print axioms demo_mul
end TranslateValue
