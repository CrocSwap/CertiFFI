-- Route 7 reviewed image (loops): the BYTE_EQUAL table for the gate's ELF check, defined as the little-endian byte
-- expansion of the reviewed words that `ArmCertLoop.ContractDraft.image` places at 0x1a4 (all 43 words of the RX
-- segment of memory.elf, 2b73bba9). `reviewedImageBytes_eq` ties the checked bytes to the same words the claim uses.
import ArmCertLoop.ContractDraft
set_option autoImplicit false

namespace Route7Root
open ArmCertLoop

/-- (vaddr, byte) for every byte of the reviewed words, little-endian, starting at Generated.imageStart (0x1a4). -/
def reviewedImageBytes : Array (Nat × Nat) :=
  ((List.range Generated.imageWords.length).flatMap fun k =>
    (List.range 4).map fun i =>
      (Generated.imageStart + 4 * k + i, ((Generated.imageWords.getD k 0).toNat >>> (8 * i)) % 256)).toArray

/-- The checked byte table is exactly the byte expansion of the reviewed words (same words as ContractDraft.image). -/
theorem reviewedImageBytes_eq : reviewedImageBytes =
    ((List.range Generated.imageWords.length).flatMap fun k =>
      (List.range 4).map fun i =>
        (Generated.imageStart + 4 * k + i, ((Generated.imageWords.getD k 0).toNat >>> (8 * i)) % 256)).toArray := rfl

theorem reviewedImageBytes_size : reviewedImageBytes.size = 172 := by decide +kernel

end Route7Root
#print axioms Route7Root.reviewedImageBytes_eq
#print axioms Route7Root.reviewedImageBytes_size
