import Sail
import Init.Omega
namespace BitFieldSummary
theorem getLsbD_update_below (x : BitVec w) (y : BitVec len) (start i : Nat)
    (h : i < start) :
    (Sail.BitVec.updateSubrange' x start len y).getLsbD i = x.getLsbD i := by
  by_cases hw : i < w
  · simp [Sail.BitVec.updateSubrange', BitVec.getLsbD_shiftLeft, h, hw,
      Nat.not_le_of_lt h]
  · rw [BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_gt hw),
      BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_gt hw)]
@[simp] theorem extract_update_below (x : BitVec w) (hi lo uhi ulo : Nat)
    (y : BitVec (uhi - ulo + 1)) (hlo : lo ≤ hi) (h : hi < ulo) :
    Sail.BitVec.extractLsb (Sail.BitVec.updateSubrange x uhi ulo y) hi lo =
      Sail.BitVec.extractLsb x hi lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases hi' : i < hi - lo + 1
  · have hpos : lo + i < ulo := by omega
    simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb',
      hi', Sail.BitVec.updateSubrange, getLsbD_update_below, hpos]
  · simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb', hi']
#print axioms extract_update_below
end BitFieldSummary
