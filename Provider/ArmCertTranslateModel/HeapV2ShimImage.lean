import ArmCertTranslateModel.HeapV2Fetch
import ArmCertTranslateModel.HeapV2ShimPlan

/-!: the decision-179 shim's code words in the relocated C9 image. For every
load base, the four image bytes at shimOffset + offset are the little-endian bytes of the shim
plan word: the memFetch-style code obligation for the shim, mirroring `fetch_code_image` for the
body. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace ArmCert.Translate.Model.HeapV2ShimPlan

theorem shim_image (base : MemReloc.Word) {code : Nat × Nat} (member : code ∈ codeWords) :
    ∀ i < 4, HeapV2.image base (shimOffset + code.1 + i) =
      some ((BitVec.ofNat 32 code.2).extractLsb' (8 * i) 8) := by
  intro i small
  have bound := (codeWords_bound code member).1
  rw [HeapV2E17.image_code base _ (by simp only [shimOffset]; omega) (by simp only [shimOffset]; omega)]
  have shift : shimOffset + code.1 + i - 0x10000 = 0x548 + code.1 + i := by simp only [shimOffset]; omega
  rw [shift]
  exact codeWords_bytes code member i small

#print axioms shim_image
end ArmCert.Translate.Model.HeapV2ShimPlan
