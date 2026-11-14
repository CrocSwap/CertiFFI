-- RtBr.BrWords: B.cond / CBZ encodings and the decode-field facts BR8 roots take (core Lean only).
set_option autoImplicit false
namespace RtBr.BrWords

def bcondWord (imm19 : BitVec 19) (cond : BitVec 4) : BitVec 32 := 84#8 ++ imm19 ++ 0#1 ++ cond
def cbzWord (sf : BitVec 1) (op : BitVec 1) (imm19 : BitVec 19) (Rt : BitVec 5) : BitVec 32 :=
  sf ++ 26#6 ++ op ++ imm19 ++ Rt

theorem bcond_inv (imm19 : BitVec 19) (cond : BitVec 4) : (bcondWord imm19 cond &&& 4278190096#32) = 1409286144#32 := by
  simp only [bcondWord, cbzWord]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_append]
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
  rcases this with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
theorem bcond_cond (imm19 : BitVec 19) (cond : BitVec 4) : BitVec.extractLsb' 0 4 (bcondWord imm19 cond) = cond := by
  simp only [bcondWord, cbzWord]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases this with h | h | h | h <;> subst h <;> simp
theorem bcond_imm19 (imm19 : BitVec 19) (cond : BitVec 4) : BitVec.extractLsb' 5 19 (bcondWord imm19 cond) = imm19 := by
  simp only [bcondWord, cbzWord]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 := by omega
  rcases this with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
theorem cbz_inv (sf : BitVec 1) (imm19 : BitVec 19) (Rt : BitVec 5) : (cbzWord sf 0#1 imm19 Rt &&& 2130706432#32) = 872415232#32 := by
  simp only [bcondWord, cbzWord]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_append]
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
  rcases this with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
theorem cbz_Rt (sf op : BitVec 1) (imm19 : BitVec 19) (Rt : BitVec 5) : BitVec.extractLsb' 0 5 (cbzWord sf op imm19 Rt) = Rt := by
  simp only [bcondWord, cbzWord]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases this with h | h | h | h | h <;> subst h <;> simp
theorem cbz_imm19 (sf op : BitVec 1) (imm19 : BitVec 19) (Rt : BitVec 5) : BitVec.extractLsb' 5 19 (cbzWord sf op imm19 Rt) = imm19 := by
  simp only [bcondWord, cbzWord]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 := by omega
  rcases this with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
theorem cbz_op (sf op : BitVec 1) (imm19 : BitVec 19) (Rt : BitVec 5) : BitVec.extractLsb' 24 1 (cbzWord sf op imm19 Rt) = op := by
  simp only [bcondWord, cbzWord]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  have : i = 0 := by omega
  subst this; simp
theorem cbz_sf (sf op : BitVec 1) (imm19 : BitVec 19) (Rt : BitVec 5) : BitVec.extractLsb' 31 1 (cbzWord sf op imm19 Rt) = sf := by
  simp only [bcondWord, cbzWord]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  have : i = 0 := by omega
  subst this; simp

end RtBr.BrWords
