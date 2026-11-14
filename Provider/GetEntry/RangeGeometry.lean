import GetEntry.NextGeometry
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 150000
namespace S1EntryRangeGeometry

theorem high_mask (x : BitVec 56) (n : Nat) :
    x &&& (BitVec.allOnes 56 <<< n) = (x >>> n) <<< n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i < n
  · simp [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, h]
  · have hidx : i - n < 56 := by omega
    have hsum : n + (i - n) = i := by omega
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, h, ↓reduceIte,
      BitVec.getLsbD_allOnes, hidx, decide_true, Bool.and_true,
      BitVec.getLsbD_ushiftRight, hi, hsum, decide_false, Bool.not_false, Bool.true_and]


theorem high_mask_zero (x : BitVec 56) (n : Nat) :
    x &&& (BitVec.allOnes 56 <<< n) = 0#56 ↔ x.toNat < 2^n := by
  rw [high_mask]
  have hx := x.isLt
  have hm := Nat.div_mul_le_self x.toNat (2^n)
  have hb : x.toNat / 2^n * 2^n < 2^56 := by omega
  have hnat : ((x >>> n) <<< n).toNat = x.toNat / 2^n * 2^n := by
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hb]
  rw [← BitVec.toNat_inj, hnat, BitVec.toNat_ofNat]
  have hp : 0 < 2^n := Nat.two_pow_pos n
  constructor
  · intro h
    have hz : x.toNat / 2^n = 0 := (Nat.mul_eq_zero.mp h).resolve_right (by omega)
    exact (Nat.div_eq_zero_iff.mp hz).resolve_left (by omega)
  · intro h
    rw [Nat.div_eq_of_lt h]
    simp

#print axioms high_mask
#print axioms high_mask_zero
theorem source_mask (x : BitVec 56) (ps : BitVec 3) :
    is_zero_subrange x 55 (S2PhysicalSizeFrame.value ps) =
      ((x &&& (BitVec.allOnes 56 <<< (S2PhysicalSizeFrame.value ps).toNat)) == 0#56) := by
  have hc : S2PhysicalSizeFrame.value ps = 32 ∨ S2PhysicalSizeFrame.value ps = 36 ∨
      S2PhysicalSizeFrame.value ps = 40 ∨ S2PhysicalSizeFrame.value ps = 42 ∨
      S2PhysicalSizeFrame.value ps = 44 ∨ S2PhysicalSizeFrame.value ps = 48 := by
    unfold S2PhysicalSizeFrame.value
    split <;> simp_all
    split <;> simp_all
    split <;> simp_all
    split <;> simp_all
    split <;> simp_all
  rcases hc with h | h | h | h | h | h
  · rw [h]
    change (x &&& slice_mask (n := 56) 32 (55 - 32 + 1) == extzv (m := 56) (0#1)) =
      (x &&& (BitVec.allOnes 56 <<< 32) == 0#56)
    have hm : slice_mask (n := 56) 32 (55 - 32 + 1) = BitVec.allOnes 56 <<< 32 := by decide
    have hz : extzv (m := 56) (0#1) = 0#56 := by decide
    rw [hm, hz]
  · rw [h]
    change (x &&& slice_mask (n := 56) 36 (55 - 36 + 1) == extzv (m := 56) (0#1)) =
      (x &&& (BitVec.allOnes 56 <<< 36) == 0#56)
    have hm : slice_mask (n := 56) 36 (55 - 36 + 1) = BitVec.allOnes 56 <<< 36 := by decide
    have hz : extzv (m := 56) (0#1) = 0#56 := by decide
    rw [hm, hz]
  · rw [h]
    change (x &&& slice_mask (n := 56) 40 (55 - 40 + 1) == extzv (m := 56) (0#1)) =
      (x &&& (BitVec.allOnes 56 <<< 40) == 0#56)
    have hm : slice_mask (n := 56) 40 (55 - 40 + 1) = BitVec.allOnes 56 <<< 40 := by decide
    have hz : extzv (m := 56) (0#1) = 0#56 := by decide
    rw [hm, hz]
  · rw [h]
    change (x &&& slice_mask (n := 56) 42 (55 - 42 + 1) == extzv (m := 56) (0#1)) =
      (x &&& (BitVec.allOnes 56 <<< 42) == 0#56)
    have hm : slice_mask (n := 56) 42 (55 - 42 + 1) = BitVec.allOnes 56 <<< 42 := by decide
    have hz : extzv (m := 56) (0#1) = 0#56 := by decide
    rw [hm, hz]
  · rw [h]
    change (x &&& slice_mask (n := 56) 44 (55 - 44 + 1) == extzv (m := 56) (0#1)) =
      (x &&& (BitVec.allOnes 56 <<< 44) == 0#56)
    have hm : slice_mask (n := 56) 44 (55 - 44 + 1) = BitVec.allOnes 56 <<< 44 := by decide
    have hz : extzv (m := 56) (0#1) = 0#56 := by decide
    rw [hm, hz]
  · rw [h]
    change (x &&& slice_mask (n := 56) 48 (55 - 48 + 1) == extzv (m := 56) (0#1)) =
      (x &&& (BitVec.allOnes 56 <<< 48) == 0#56)
    have hm : slice_mask (n := 56) 48 (55 - 48 + 1) = BitVec.allOnes 56 <<< 48 := by decide
    have hz : extzv (m := 56) (0#1) = 0#56 := by decide
    rw [hm, hz]


theorem in_range (wp : S1TTWParams) (slot : FullAddress) :
    S1TablePrefix10.outOfRange wp slot = false ↔
      slot.address.toNat < 2^(S2PhysicalSizeFrame.value wp.ps).toNat := by
  unfold S1TablePrefix10.outOfRange
  rw [source_mask]
  change (Bool.not ((slot.address &&& (BitVec.allOnes 56 <<< (S2PhysicalSizeFrame.value wp.ps).toNat)) == 0#56) = false) ↔ _
  have hn (b : Bool) : Bool.not b = false ↔ b = true := by cases b <;> decide
  rw [hn, beq_iff_eq]
  exact high_mask_zero _ _
#print axioms source_mask
#print axioms in_range
end S1EntryRangeGeometry

