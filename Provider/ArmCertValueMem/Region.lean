-- Memory: generic region facts over ArmCertValue.Core (ArmCert-only).
import HeapV2StepCerts.RegBindCore
import ArmCertValue.Core
set_option autoImplicit false
namespace ArmCertValue.MemRegion
open ArmCertValue HeapV2StepCerts.RegBind

/-- Byte k of a 64-bit word. -/
def byteOf (v : BitVec 64) (k : Nat) : BitVec 8 := (v >>> (8 * k)).setWidth 8

theorem byteOf_getLsbD (v : BitVec 64) (k i : Nat) (hi : i < 8) :
    (byteOf v k).getLsbD i = v.getLsbD (8 * k + i) := by
  unfold byteOf
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]

/-- Reassembling a word's 8 bytes gives the word. -/
theorem asm_byteOf (v : BitVec 64) :
    ((((((((0#64 ||| (byteOf v 7).setWidth 64 <<< 56) ||| (byteOf v 6).setWidth 64 <<< 48) |||
      (byteOf v 5).setWidth 64 <<< 40) ||| (byteOf v 4).setWidth 64 <<< 32) ||| (byteOf v 3).setWidth 64 <<< 24) |||
      (byteOf v 2).setWidth 64 <<< 16) ||| (byteOf v 1).setWidth 64 <<< 8) ||| (byteOf v 0).setWidth 64 <<< 0) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, byteOf, BitVec.getLsbD_ushiftRight]

/-- Byte k of an assembled word. -/
theorem byteOf_asm (b : Nat → BitVec 8) (k : Nat) (hk : k < 8) :
    byteOf ((((((((0#64 ||| (b 7).setWidth 64 <<< 56) ||| (b 6).setWidth 64 <<< 48) ||| (b 5).setWidth 64 <<< 40) |||
      (b 4).setWidth 64 <<< 32) ||| (b 3).setWidth 64 <<< 24) ||| (b 2).setWidth 64 <<< 16) |||
      (b 1).setWidth 64 <<< 8) ||| (b 0).setWidth 64 <<< 0) k = b k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [byteOf_getLsbD _ _ _ hi]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]


/-- Sail's Int shift at a natural amount is the Nat shift. -/
theorem shl_int (x : BitVec 64) (k : Nat) : x <<< (8 * (k : Int)) = x <<< (8 * k) := rfl

/-- A byte read at word w, byte k, with the VA in regionWord's form. -/
theorem regionByte_at (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (s : St) (r : Region) (w k : Nat) :
    regionByte mapping pinv s r (8 * w + k) =
      (mapping (BitVec.ofInt 64 ((pinv r.pin : Int) + r.off + 8 * (w : Int) + (k : Int)))).bind fun pa => s.mem[pa]? := by
  unfold regionByte
  have hva : (pinv r.pin : Int) + r.off + ((8 * w + k : Nat) : Int) = (pinv r.pin : Int) + r.off + 8 * (w : Int) + (k : Int) := by
    simp only [Int.natCast_add, Int.natCast_mul]; omega
  rw [hva]

theorem regionWord_bytes (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (s : St) (r : Region) (w : Nat)
    (v : BitVec 64) :
    regionWord mapping pinv s r w = some v ↔
      ∀ k, k < 8 → regionByte mapping pinv s r (8 * w + k) = some ((v >>> (8 * k)).setWidth 8) := by
  simp only [regionWord, List.range, List.range.loop, List.map, List.foldr, bind, pure]
  simp only [← Option.bind_assoc]
  have e : ∀ k : Nat, ((mapping (BitVec.ofInt 64 ((pinv r.pin : Int) + r.off + 8 * (w : Int) + (k : Int)))).bind
      fun pa => s.mem[pa]?) = regionByte mapping pinv s r (8 * w + k) := fun k => (regionByte_at mapping pinv s r w k).symm
  simp only [e]
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
    have h' : ∀ k, k < 8 → regionByte mapping pinv s r (8 * w + k) = some (byteOf v k) := h
    rw [show 8 * w = 8 * w + 0 from rfl, h' 0 (by decide), h' 1 (by decide), h' 2 (by decide), h' 3 (by decide),
      h' 4 (by decide), h' 5 (by decide), h' 6 (by decide), h' 7 (by decide)]
    simp only [Option.bind_some, Option.some.injEq, shl_int, Nat.reduceMul]
    exact asm_byteOf v


/-- **Word frame from the byte frame**: equal bytes 8w..8w+7 give equal word reads. -/
theorem regionWord_congr (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (x y : St) (r : Region) (w : Nat)
    (h : ∀ k, k < 8 → regionByte mapping pinv y r (8 * w + k) = regionByte mapping pinv x r (8 * w + k)) :
    regionWord mapping pinv y r w = regionWord mapping pinv x r w := by
  simp only [regionWord, List.range, List.range.loop, List.map, List.foldr, bind, pure]
  simp only [← Option.bind_assoc]
  have e : ∀ (z : St) (k : Nat), ((mapping (BitVec.ofInt 64 ((pinv r.pin : Int) + r.off + 8 * (w : Int) + (k : Int)))).bind
      fun pa => z.mem[pa]?) = regionByte mapping pinv z r (8 * w + k) := fun z k => (regionByte_at mapping pinv z r w k).symm
  simp only [e]
  rw [show 8 * w = 8 * w + 0 from rfl, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
    h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]

#print axioms regionWord_bytes
#print axioms regionWord_congr
#print axioms asm_byteOf
#print axioms byteOf_asm
end ArmCertValue.MemRegion
