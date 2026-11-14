import Bridge.BvField
open BitVec
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to CryptoBridge.SubsImmDecodeLNSym.
namespace CryptoBridge.AddSubImm


/-- The ADD/ADDS/SUB/SUBS (immediate) word built from its fields. -/
def addSubImmWord (sf op S sh : BitVec 1) (imm12 : BitVec 12) (Rn Rd : BitVec 5) : BitVec 32 :=
  sf ++ op ++ S ++ 34#6 ++ sh ++ imm12 ++ Rn ++ Rd

/-- The caller-word premises of the SUBS-immediate root, for the word itself. -/
theorem subsImm_mask (sf sh : BitVec 1) (imm12 : BitVec 12) (Rn Rd : BitVec 5) :
    (addSubImmWord sf 1#1 1#1 sh imm12 Rn Rd &&& 2139095040#32) = 1895825408#32 := by
  unfold addSubImmWord
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_append]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem f_Rd (sf op S sh : BitVec 1) (imm12 : BitVec 12) (Rn Rd : BitVec 5) :
    BitVec.extractLsb' 0 5 (addSubImmWord sf op S sh imm12 Rn Rd) = Rd := by unfold addSubImmWord; bv_field

theorem f_Rn (sf op S sh : BitVec 1) (imm12 : BitVec 12) (Rn Rd : BitVec 5) :
    BitVec.extractLsb' 5 5 (addSubImmWord sf op S sh imm12 Rn Rd) = Rn := by unfold addSubImmWord; bv_field

theorem f_imm12 (sf op S sh : BitVec 1) (imm12 : BitVec 12) (Rn Rd : BitVec 5) :
    BitVec.extractLsb' 10 12 (addSubImmWord sf op S sh imm12 Rn Rd) = imm12 := by unfold addSubImmWord; bv_field

theorem f_sh (sf op S sh : BitVec 1) (imm12 : BitVec 12) (Rn Rd : BitVec 5) :
    BitVec.extractLsb' 22 1 (addSubImmWord sf op S sh imm12 Rn Rd) = sh := by unfold addSubImmWord; bv_field

theorem f_S (sf op S sh : BitVec 1) (imm12 : BitVec 12) (Rn Rd : BitVec 5) :
    BitVec.extractLsb' 29 1 (addSubImmWord sf op S sh imm12 Rn Rd) = S := by unfold addSubImmWord; bv_field

theorem f_op (sf op S sh : BitVec 1) (imm12 : BitVec 12) (Rn Rd : BitVec 5) :
    BitVec.extractLsb' 30 1 (addSubImmWord sf op S sh imm12 Rn Rd) = op := by unfold addSubImmWord; bv_field

theorem f_sf (sf op S sh : BitVec 1) (imm12 : BitVec 12) (Rn Rd : BitVec 5) :
    BitVec.extractLsb' 31 1 (addSubImmWord sf op S sh imm12 Rn Rd) = sf := by unfold addSubImmWord; bv_field

end CryptoBridge.AddSubImm

