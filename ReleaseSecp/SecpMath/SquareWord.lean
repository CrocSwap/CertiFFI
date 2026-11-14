import SecpMath.WordMulAdd
import Lean.Elab.Tactic.Grind
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SecpMath.SquareWord
open ArmCertValue SecpMath.Product SecpMath.Addition

theorem square_expansion (a b c d : Nat) :
    pack4 a b c d * pack4 a b c d =
      a*a + limbRadix^2*(b*b) + limbRadix^4*(c*c) + limbRadix^6*(d*d) +
      2*limbRadix*(a*b + limbRadix*(a*c) + limbRadix^2*(a*d+b*c) +
        limbRadix^3*(b*d) + limbRadix^4*(c*d)) := by
  unfold pack4
  grind

theorem high_add (x y carry : BitVec 64) (bound : carry.toNat ≤ 1) :
    (Op.add3.eval [Op.umulh.eval [x,y],0#64,carry]).toNat =
      (Op.umulh.eval [x,y]).toNat + carry.toNat := by
  have high := Product.umulh_le x y
  have fit : (Op.umulh.eval [x,y]).toNat + carry.toNat < limbRadix := by
    have positive : 2 ≤ limbRadix := by decide
    omega
  rw [WordMulAdd.add3_nat]
  simpa only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero] using Nat.mod_eq_of_lt fit

#print axioms square_expansion
#print axioms high_add
end SecpMath.SquareWord
