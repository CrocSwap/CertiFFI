import Walk.S1OuterStep
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 300000
namespace S1StablePath

theorem bit_eq (x y : BitVec 64) (h : S1Descriptor.stable x = S1Descriptor.stable y)
    (i : Nat) (hi : i < 64) (h7 : i ≠ 7) (h10 : i ≠ 10) :
    x.getLsbD i = y.getLsbD i := by
  have mask (n : Nat) (hne : i ≠ n) : ((1#64) <<< n).getLsbD i = false := by
    simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one]
    by_cases hl : i < n
    · simp [hl]
    · have hz : i - n ≠ 0 := by omega
      simp [hl, hz]
  have hb := congrArg (fun d : BitVec 64 => d.getLsbD i) h
  simpa only [S1Descriptor.stable, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_or, mask 7 h7, mask 10 h10, hi, decide_true, Bool.false_or,
    Bool.not_false, Bool.and_true, Bool.true_and] using hb

theorem classify_eq (x y : BitVec 64) (level : Int)
    (h : S1Descriptor.stable x = S1Descriptor.stable y) :
    S1DecodeFacts.classify x level = S1DecodeFacts.classify y level := by
  have h0 := bit_eq x y h 0 (by decide) (by decide) (by decide)
  have h1 := bit_eq x y h 1 (by decide) (by decide) (by decide)
  have h0b : x[0]! = y[0]! := by
    simpa [getElem!_def, ← BitVec.getLsbD_eq_getElem] using h0
  have h1b : x[1]! = y[1]! := by
    simpa [getElem!_def, ← BitVec.getLsbD_eq_getElem] using h1
  have b0 : S1DecodeFacts.bit x 0 = S1DecodeFacts.bit y 0 := by
    unfold S1DecodeFacts.bit Sail.BitVec.access
    rw [h0b]
  have b1 : S1DecodeFacts.bit x 1 = S1DecodeFacts.bit y 1 := by
    unfold S1DecodeFacts.bit Sail.BitVec.access
    rw [h1b]
  simp only [S1DecodeFacts.classify, b0, b1]
theorem table_base_eq (x y : BitVec 64)
    (h : S1Descriptor.stable x = S1Descriptor.stable y) :
    S1NextTable10Facts.base x = S1NextTable10Facts.base y := by
  have he : x.extractLsb' 12 36 = y.extractLsb' 12 36 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    exact bit_eq x y h (12 + i) (by omega) (by omega) (by omega)
  change Sail.BitVec.updateSubrange (0#56) 47 12 (x.extractLsb' 12 36) =
    Sail.BitVec.updateSubrange (0#56) 47 12 (y.extractLsb' 12 36)
  rw [he]
#print axioms classify_eq
#print axioms table_base_eq

end S1StablePath
