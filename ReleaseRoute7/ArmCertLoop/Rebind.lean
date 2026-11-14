import ArmCertValue.Physical

open ArmCertValue
open HeapV2StepCerts.RegBind (Reg St regVal)

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

namespace ArmCertLoop.Rebind

/-- Exactly one physical byte is visible, regardless of the Region carrier's
nominal word capacity. Offsets other than zero have no mapping. -/
def oneBytePA (tag : Region) (pa : Nat) : Physical.BytePA :=
  fun r j => if r = tag ∧ j = 0 then some pa else none

/-- A block-local symbolic view tracks registers and exactly one byte. There
are no word or NZCV bindings and no padding-byte presence obligations. -/
def oneByteSym (regs : Reg → Option Nat) (tag : Region) (byteId : Nat) : Sym :=
  ⟨regs, none, fun r j => if r = tag ∧ j = 0 then some (byteId, 0) else none⟩

theorem byte_at_zero (tag : Region) (pa : Nat) (x : St) :
    Physical.regionByte (oneBytePA tag pa) x tag 0 = x.mem[pa]? := by
  simp [Physical.regionByte, oneBytePA]

theorem other_byte_absent (tag r : Region) (pa j : Nat) (different : r ≠ tag ∨ j ≠ 0) (x : St) :
    Physical.regionByte (oneBytePA tag pa) x r j = none := by
  simp only [Physical.regionByte, oneBytePA]
  have outside : ¬ (r = tag ∧ j = 0) := by
    intro inside
    rcases different with hr | hj
    · exact hr inside.1
    · exact hj inside.2
  simp [outside]

/-- Re-establish local SSA agreement from actual current registers and one
actual current byte. This conditional adapter must be applied inside the loop
proof; its equations are not caller obligations in a public card. -/
theorem agrees_one_byte (tag : Region) (pa byteId : Nat) (regs : Reg → Option Nat)
    (vals : List (BitVec 64)) (x : St)
    (registers : ∀ r i, regs r = some i → regVal x r = vals.getD i 0)
    (present : x.mem[pa]? = some ((vals.getD byteId 0).setWidth 8)) :
    Physical.Agrees (oneBytePA tag pa) vals (oneByteSym regs tag byteId) x := by
  refine ⟨registers, ?_, ?_⟩
  · intro n z c v h; cases h
  · intro r j i k tracked
    change (if r = tag ∧ j = 0 then some (byteId, 0) else none) = some (i, k) at tracked
    split at tracked
    · next inside =>
      obtain ⟨rfl, rfl⟩ := inside
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj tracked)
      simpa only [byte_at_zero, Nat.mul_zero, BitVec.ushiftRight_zero] using present
    · cases tracked

/-- The same sparse symbolic binding works inside a larger byte view, e.g.
one that also maps the store destination. Untracked bytes need no presence. -/
theorem agrees_one_byte_in_view (bytePA : Physical.BytePA) (tag : Region)
    (byteId : Nat) (regs : Reg → Option Nat) (vals : List (BitVec 64)) (x : St)
    (registers : ∀ r i, regs r = some i → regVal x r = vals.getD i 0)
    (present : Physical.regionByte bytePA x tag 0 = some ((vals.getD byteId 0).setWidth 8)) :
    Physical.Agrees bytePA vals (oneByteSym regs tag byteId) x := by
  refine ⟨registers, ?_, ?_⟩
  · intro n z c v h; cases h
  · intro r j i k tracked
    change (if r = tag ∧ j = 0 then some (byteId, 0) else none) = some (i, k) at tracked
    split at tracked
    · next inside =>
      obtain ⟨rfl, rfl⟩ := inside
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj tracked)
      simpa only [Nat.mul_zero, BitVec.ushiftRight_zero] using present
    · cases tracked

theorem bounded_one_byte (tag : Region) (byteId n : Nat) (regs : Reg → Option Nat)
    (registers : ∀ r i, regs r = some i → i < n) (byteBound : byteId < n) :
    (oneByteSym regs tag byteId).Bounded n := by
  refine ⟨registers, ?_, ?_⟩
  · intro a b c d h; cases h
  · intro r j i k tracked
    change (if r = tag ∧ j = 0 then some (byteId, 0) else none) = some (i, k) at tracked
    split at tracked
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj tracked)
      exact byteBound
    · cases tracked

#print axioms byte_at_zero
#print axioms other_byte_absent
#print axioms agrees_one_byte
#print axioms agrees_one_byte_in_view
#print axioms bounded_one_byte

end ArmCertLoop.Rebind
