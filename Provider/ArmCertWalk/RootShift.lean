import ArmCertWalk.RootAlignmentNat
import ArmCertWalk.RootEntryIndex

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

theorem source_shiftl_nat (value : Int) (amount : Nat) :
    Sail.Int.shiftl value (amount : Int) = value * 2^amount := by
  change Sail.Nat.iterate (fun x : Int => x * 2) amount value = _
  induction amount generalizing value with
  | zero =>
    change value = value * 1
    simp only [Int.mul_one]
  | succ amount ih =>
    change Sail.Nat.iterate (fun x : Int => x * 2) amount (value * 2) = _
    rw [ih]
    simp [Int.pow_succ, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

theorem source_shift_one (amount : Nat) :
    _shl_int_general 1 (amount : Int) = ((2^amount : Nat) : Int) := by
  have nonnegative : 0 ≤ (amount : Int) := by omega
  simp [_shl_int_general, nonnegative, Sail.Int.toNatChecked, source_shiftl_nat]

theorem current_root_aligned (layout : S1LogicalReference.Layout) (params : S1TTWParams)
    (va : BitVec 64) (registers : Regs) (current : CurrentLayoutAt layout params va registers)
    (level : layout.start ≤ 3) :
    layout.root.toNat % 2 ^ (S1LogicalReference.rootBits layout.start layout.inputBits + 3) = 0 := by
  have geometry := current_root_geometry layout params va registers current level
  have aligned := align_bits_mod
    (Sail.BitVec.updateSubrange (0#56) 47 1
      (Sail.BitVec.extractLsb (selectedRootTTBR registers va) 47 1))
    (2 ^ (S1LogicalReference.rootBits layout.start layout.inputBits + 3)) (by exact Nat.pow_pos (by decide))
  have size : rootTableSize params =
      ((S1LogicalReference.rootBits layout.start layout.inputBits + 3 : Nat) : Int) := by
    simpa using geometry.2.2
  have root := current.root
  unfold rootBaseValue at root
  rw [size, source_shift_one] at root
  have base := congrArg BitVec.toNat root
  rw [BitVec.toNat_setWidth_of_le (by decide)] at base
  rw [base]
  exact aligned

#print axioms source_shiftl_nat
#print axioms source_shift_one
#print axioms current_root_aligned

end ArmCertWalk
