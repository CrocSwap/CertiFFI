import ArmCertValue.Physical
import ArmCertValueMem.Region
set_option autoImplicit false
namespace ArmCertValue.Physical
open HeapV2StepCerts.RegBind (Reg St regVal)
open ArmCertValue.MemRegion (byteOf byteOf_asm asm_byteOf shl_int)

theorem regionWord_bytes (bytePA : BytePA) (s : St) (r : Region) (w : Nat)
    (v : BitVec 64) :
    regionWord bytePA s r w = some v ↔
      ∀ k, k < 8 → regionByte bytePA s r (8 * w + k) = some ((v >>> (8 * k)).setWidth 8) := by
  simp only [regionWord, List.range, List.range.loop, List.map, List.foldr, bind, pure]
  constructor
  · intro h k hk
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨b0, h0, a1, ⟨b1, h1, a2, ⟨b2, h2, a3, ⟨b3, h3, a4, ⟨b4, h4, a5, ⟨b5, h5, a6, ⟨b6, h6, a7,
      ⟨b7, h7, a8, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
    simp only [shl_int, Nat.reduceMul]
    have A := fun K (hK : K < 8) => (byteOf_asm (fun i => [b0, b1, b2, b3, b4, b5, b6, b7].getD i 0) K hK).symm
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h0]; exact congrArg some (A 0 (by decide))
    · rw [h1]; exact congrArg some (A 1 (by decide))
    · rw [h2]; exact congrArg some (A 2 (by decide))
    · rw [h3]; exact congrArg some (A 3 (by decide))
    · rw [h4]; exact congrArg some (A 4 (by decide))
    · rw [h5]; exact congrArg some (A 5 (by decide))
    · rw [h6]; exact congrArg some (A 6 (by decide))
    · rw [h7]; exact congrArg some (A 7 (by decide))
  · intro h
    have h' : ∀ k, k < 8 → regionByte bytePA s r (8 * w + k) = some (byteOf v k) := h
    rw [show 8 * w = 8 * w + 0 from rfl, h' 0 (by decide), h' 1 (by decide), h' 2 (by decide), h' 3 (by decide),
      h' 4 (by decide), h' 5 (by decide), h' 6 (by decide), h' 7 (by decide)]
    simp only [Option.bind_some, Option.some.injEq, shl_int, Nat.reduceMul]
    exact asm_byteOf v


/-- **Word frame from the byte frame**: equal bytes 8w..8w+7 give equal word reads. -/
theorem regionWord_congr (bytePA : BytePA) (x y : St) (r : Region) (w : Nat)
    (h : ∀ k, k < 8 → regionByte bytePA y r (8 * w + k) = regionByte bytePA x r (8 * w + k)) :
    regionWord bytePA y r w = regionWord bytePA x r w := by
  simp only [regionWord, List.range, List.range.loop, List.map, List.foldr, bind, pure]
  rw [show 8 * w = 8 * w + 0 from rfl, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
    h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]


#print axioms regionWord_bytes
#print axioms regionWord_congr
end ArmCertValue.Physical
