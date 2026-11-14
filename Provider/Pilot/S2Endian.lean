import Pilot.S2Bytes
import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace S2Endian

def reversedBytes (d : BitVec 64) : BitVec 64 :=
  BitVec.append (d.extractLsb' 0 8)
    (BitVec.append (d.extractLsb' 8 8)
      (BitVec.append (d.extractLsb' 16 8)
        (BitVec.append (d.extractLsb' 24 8)
          (BitVec.append (d.extractLsb' 32 8)
            (BitVec.append (d.extractLsb' 40 8)
              (BitVec.append (d.extractLsb' 48 8) (d.extractLsb' 56 8)))))))

theorem reverse_eq (d : BitVec 64) : reverse_endianness d = reversedBytes d := by rfl

theorem reverse_byte (d : BitVec 64) (i : Nat) (hi : i < 8) :
    (reverse_endianness d).extractLsb' (8 * i) 8 = d.extractLsb' (8 * (7 - i)) 8 := by
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  all_goals
    simp only [reverse_eq, reversedBytes, BitVec.append, BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_or, BitVec.getLsbD_setWidth', BitVec.getLsbD_shiftLeftZeroExtend]
    have hjc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    rcases hjc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ext_bytes (x y : BitVec 64)
    (h : ∀ i : Nat, i < 8 → x.extractLsb' (8 * i) 8 = y.extractLsb' (8 * i) 8) : x = y := by
  have hx := S2Bytes.join64 x
  rw [h 7 (by decide), h 6 (by decide), h 5 (by decide), h 4 (by decide),
    h 3 (by decide), h 2 (by decide), h 1 (by decide), h 0 (by decide)] at hx
  exact hx.symm.trans (S2Bytes.join64 y)

theorem reverse_involutive (d : BitVec 64) :
    reverse_endianness (reverse_endianness d) = d := by
  apply ext_bytes
  intro i hi
  rw [reverse_byte _ i hi, reverse_byte d (7 - i) (by omega)]
  have hk : 7 - (7 - i) = i := by omega
  rw [hk]

def encode (ee : BitVec 1) (d : BitVec 64) : BitVec 64 :=
  if ee = 1#1 then reverse_endianness d else d

theorem encode_involutive (ee : BitVec 1) (d : BitVec 64) : encode ee (encode ee d) = d := by
  by_cases h : ee = 1#1 <;> simp [encode, h, reverse_involutive]

#print axioms reverse_byte
#print axioms reverse_involutive
end S2Endian
