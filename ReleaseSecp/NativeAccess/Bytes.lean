import NativeAccess.Trace
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 4096
namespace NativeAccess.Bytes

/-- Bounded slices compose without introducing zero-extension bytes. -/
theorem extract_compose {w : Nat} (v : BitVec w) (base len off len2 : Nat)
    (fits : off + len2 ≤ len) :
    (v.extractLsb' base len).extractLsb' off len2 = v.extractLsb' (base + off) len2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hlen : off + j < len := by omega
  simp only [BitVec.getLsbD_extractLsb',hj,hlen,decide_true,Bool.true_and]
  rw [Nat.add_assoc]

def high64 (v : BitVec 128) : BitVec 64 :=
  Sail.BitVec.castWidth (Sail.BitVec.extractLsb v 127 64)

def low64 (v : BitVec 128) : BitVec 64 :=
  Sail.BitVec.castWidth (Sail.BitVec.extractLsb v 63 0)

theorem high64_byte (v : BitVec 128) (i : Nat) (hi : i < 8) :
    (high64 v).extractLsb' (8 * i) 8 = v.extractLsb' (8 * (8 + i)) 8 := by
  change (v.extractLsb' 64 64).extractLsb' (8 * i) 8 = _
  rw [extract_compose v 64 64 (8 * i) 8 (by omega)]
  congr 1
  omega

theorem low64_byte (v : BitVec 128) (i : Nat) (hi : i < 8) :
    (low64 v).extractLsb' (8 * i) 8 = v.extractLsb' (8 * i) 8 := by
  change (v.extractLsb' 0 64).extractLsb' (8 * i) 8 = _
  simpa only [Nat.zero_add] using extract_compose v 0 64 (8 * i) 8 (by omega)

theorem checked_nat (n : Nat) : Sail.Int.toNatChecked (n : Int) = n := by
  simp [Sail.Int.toNatChecked]

theorem castWidth_eq_cast {n m : Nat} (h : n = m) (v : BitVec n) :
    Sail.BitVec.castWidth (m := m) v = v.cast h := by
  cases h
  exact Sail.BitVec.castWidth_eq v

theorem updateSubrange_cast {w n m : Nat} (v : BitVec w) (base : Nat)
    (b : BitVec n) (h : n = m) :
    Sail.BitVec.updateSubrange' v base m (b.cast h) = Sail.BitVec.updateSubrange' v base n b := by
  cases h
  rfl

/-- The exact slice/cast emitted by Sail for byte i. -/
theorem sail_byte {w : Nat} (v : BitVec w) (i : Nat) :
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb v
      (Sail.Int.toNatChecked ((8 : Int) * (i : Int) + 7))
      (Sail.Int.toNatChecked ((8 : Int) * (i : Int)))) : BitVec 8) =
      v.extractLsb' (8 * i) 8 := by
  have low : (8 : Int) * (i : Int) = ((8 * i : Nat) : Int) := by omega
  have high : (8 : Int) * (i : Int) + 7 = ((8 * i + 7 : Nat) : Int) := by omega
  have width : 8 * i + 7 - 8 * i + 1 = 8 := by omega
  rw [high,low,checked_nat,checked_nat]
  unfold Sail.BitVec.extractLsb BitVec.extractLsb
  rw [castWidth_eq_cast width]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_cast,BitVec.getLsbD_extractLsb',width]


theorem sail_byte_int {w : Nat} (v : BitVec w) (i : Int) (nonneg : 0 ≤ i) :
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb v
      (Sail.Int.toNatChecked (8 * i + 7)) (Sail.Int.toNatChecked (8 * i))) : BitVec 8) =
      v.extractLsb' (8 * i.toNat) 8 := by
  cases i with
  | ofNat n => exact sail_byte v n
  | negSucc n => omega

/-- Pure word update performed by the real byte-read loops. -/
def setByte {w : Nat} (v : BitVec w) (i : Nat) (b : BitVec 8) : BitVec w :=
  Sail.BitVec.updateSubrange' v (8 * i) 8 b

theorem sail_setByte {w : Nat} (v : BitVec w) (i : Nat) (b : BitVec 8) :
    Sail.BitVec.updateSubrange v (8 * i + 7) (8 * i) (Sail.BitVec.castWidth b) = setByte v i b := by
  have width : 8 * i + 7 - 8 * i + 1 = 8 := by omega
  unfold Sail.BitVec.updateSubrange setByte
  rw [castWidth_eq_cast width.symm]
  exact updateSubrange_cast v (8 * i) b width.symm

theorem sail_setByte_indices {w : Nat} (v : BitVec w) (i : Nat) (b : BitVec 8) :
    Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((8 : Int) * (i : Int) + 7))
      (Sail.Int.toNatChecked ((8 : Int) * (i : Int))) (Sail.BitVec.castWidth b) = setByte v i b := by
  have low : (8 : Int) * (i : Int) = ((8 * i : Nat) : Int) := by omega
  have high : (8 : Int) * (i : Int) + 7 = ((8 * i + 7 : Nat) : Int) := by omega
  rw [high,low,checked_nat,checked_nat]
  exact sail_setByte v i b

theorem sail_setByte_int {w : Nat} (v : BitVec w) (i : Int) (nonneg : 0 ≤ i) (b : BitVec 8) :
    Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked (8 * i + 7))
      (Sail.Int.toNatChecked (8 * i)) (Sail.BitVec.castWidth b) = setByte v i.toNat b := by
  cases i with
  | ofNat n => exact sail_setByte_indices v n b
  | negSucc n => omega

theorem setByte_bit {w : Nat} (v : BitVec w) (i : Nat) (b : BitVec 8)
    (j : Nat) (hj : j < w) :
    (setByte v i b).getLsbD j =
      if 8 * i ≤ j ∧ j < 8 * i + 8 then b.getLsbD (j - 8 * i) else v.getLsbD j := by
  simp only [setByte,Sail.BitVec.updateSubrange',BitVec.getLsbD_or,BitVec.getLsbD_and,
    BitVec.getLsbD_not,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_setWidth,
    BitVec.getLsbD_allOnes,hj,decide_true,Bool.true_and]
  by_cases before : j < 8 * i
  · simp [before,show ¬ (8 * i ≤ j ∧ j < 8 * i + 8) by omega]
  · have hsmall : j - 8 * i < w := by omega
    by_cases inside : j < 8 * i + 8
    · have hbyte : j - 8 * i < 8 := by omega
      simp [before,inside,hsmall,hbyte,show 8 * i ≤ j by omega]
    · have hbyte : 8 ≤ j - 8 * i := by omega
      simp [before,inside,hsmall,hbyte,BitVec.getLsbD_of_ge b _ hbyte]

def fill {w : Nat} (initial target : BitVec w) : Nat → BitVec w
  | 0 => initial
  | k + 1 => setByte (fill initial target k) k (target.extractLsb' (8 * k) 8)

theorem fill_prefix {w : Nat} (initial target : BitVec w) (k : Nat)
    (j : Nat) (hj : j < w) (written : j < 8 * k) :
    (fill initial target k).getLsbD j = target.getLsbD j := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [fill,setByte_bit _ _ _ j hj]
    by_cases old : j < 8 * k
    · rw [if_neg (by omega)]
      exact ih old
    · rw [if_pos (by omega)]
      have hb : j - 8 * k < 8 := by omega
      simp only [BitVec.getLsbD_extractLsb',hb,decide_true,Bool.true_and]
      congr 1
      omega

/-- Every bit is overwritten by the actual byte-update operation, independent
of the initial undefined word. This applies to both 8- and 16-byte values. -/
theorem fill_word (n : Nat) (initial target : BitVec (n * 8)) : fill initial target n = target := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact fill_prefix initial target n j hj (by omega)

#print axioms high64_byte
#print axioms low64_byte
#print axioms sail_byte
#print axioms sail_byte_int
#print axioms sail_setByte_int
#print axioms sail_setByte
#print axioms fill_word
end NativeAccess.Bytes
