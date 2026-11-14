import ArmCertWalk.RootShift

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

theorem root_entry_layout_index (layout : S1LogicalReference.Layout) (params : S1TTWParams)
    (va : BitVec 64) (registers : Regs) (current : CurrentLayoutAt layout params va registers)
    (level : layout.start ≤ 3) :
    (rootEntryIndex params (layout.start : Int) va).toNat =
      8 * S1LogicalReference.entryIndex va layout.start
        (S1LogicalReference.rootBits layout.start layout.inputBits) := by
  rw [root_entry_index_toNat params _ va
    (current_layout_entry_bounds layout params va registers current level)]
  have geometry := current_root_geometry layout params va registers current level
  have input := current.inputBits
  have low : (rootEntryLow (layout.start : Int)).toNat = 12 + 9 * (3 - layout.start) := by
    unfold rootEntryLow
    omega
  have bits : (rootEntryHigh params).toNat - (rootEntryLow (layout.start : Int)).toNat + 1 =
      S1LogicalReference.rootBits layout.start layout.inputBits := by
    unfold rootEntryHigh S1LogicalReference.rootBits
    rw [← current.inputBits, low]
    unfold S1LogicalReference.rootBits at geometry
    omega
  rw [bits, low]
  rfl

theorem aligned_or_index (base index bits : Nat) (aligned : base % 2^bits = 0)
    (bound : index < 2^bits) : base ||| index = base + index := by
  have baseEq : base = (base / 2^bits) <<< bits := by
    rw [Nat.shiftLeft_eq]
    exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero aligned)).symm
  rw [baseEq]
  exact (Nat.shiftLeft_add_eq_or_of_lt bound _).symm

theorem root_entry_slot_projection (layout : S1LogicalReference.Layout) (params : S1TTWParams)
    (va : BitVec 64) (registers : Regs) (current : CurrentLayoutAt layout params va registers)
    (level : layout.start ≤ 3) (base : FullAddress)
    (address : base.address = layout.root.setWidth 56) :
    (rootEntryValue params (layout.start : Int) va base).address.toNat =
      S1LogicalReference.entryAddress layout.root va layout.start
        (S1LogicalReference.rootBits layout.start layout.inputBits) := by
  have index := root_entry_layout_index layout params va registers current level
  have modBound : S1LogicalReference.entryIndex va layout.start
      (S1LogicalReference.rootBits layout.start layout.inputBits) <
      2 ^ (S1LogicalReference.rootBits layout.start layout.inputBits) :=
    Nat.mod_lt _ (Nat.pow_pos (by decide))
  have bound : (rootEntryIndex params (layout.start : Int) va).toNat <
      2 ^ (S1LogicalReference.rootBits layout.start layout.inputBits + 3) := by
    rw [index, Nat.pow_add]
    change 8 * S1LogicalReference.entryIndex va layout.start
      (S1LogicalReference.rootBits layout.start layout.inputBits) <
      2 ^ (S1LogicalReference.rootBits layout.start layout.inputBits) * 8
    omega
  have baseNat : base.address.toNat = layout.root.toNat := by
    rw [address, BitVec.toNat_setWidth_of_le (by decide)]
  change (base.address ||| rootEntryIndex params (layout.start : Int) va).toNat = _
  rw [BitVec.toNat_or, baseNat,
    aligned_or_index _ _ _ (current_root_aligned layout params va registers current level) bound, index]
  rfl

#print axioms root_entry_layout_index
#print axioms aligned_or_index
#print axioms root_entry_slot_projection

end ArmCertWalk
