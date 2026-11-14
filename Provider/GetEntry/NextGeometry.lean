import GetEntry.RootGeometry
import Walk.S1ReferenceKind
import Walk.S1ResourcePath
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 150000
namespace S1EntryNextGeometry

theorem address (base : FullAddress) (va : BitVec 64) (level : Nat) (hl : level ≤ 3)
    (halign : base.address.toNat % 4096 = 0)
    (hwidth : base.address.toNat < 2^48) :
    (S2NextEntryFrame.address (level : Int) va base).address.toNat =
      S1LogicalReference.entryAddress (base.address.setWidth 48) va level 9 := by
  have h (shift : Nat) := S1EntryGeometry.aligned_or_index base.address
    (va.extractLsb' shift 9) halign
  have hc : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  all_goals
    simp [S2NextEntryFrame.address, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb,
      Sail.Int.toNatChecked, BitVec.extractLsb, BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, S1LogicalReference.entryAddress, S1LogicalReference.entryIndex,
      BitVec.toNat_setWidth, Nat.mod_eq_of_lt hwidth, BitVec.toNat_append, Nat.shiftLeft_eq, Sail.BitVec.append', Sail.BitVec.castWidth, BitVec.instHAppendHAddNat, HAppend.hAppend, -BitVec.append_eq]
  · simpa [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_append, Nat.shiftLeft_eq, Sail.BitVec.append', Sail.BitVec.castWidth, BitVec.instHAppendHAddNat, HAppend.hAppend, -BitVec.append_eq] using h 39
  · simpa [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_append, Nat.shiftLeft_eq, Sail.BitVec.append', Sail.BitVec.castWidth, BitVec.instHAppendHAddNat, HAppend.hAppend, -BitVec.append_eq] using h 30
  · simpa [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_append, Nat.shiftLeft_eq, Sail.BitVec.append', Sail.BitVec.castWidth, BitVec.instHAppendHAddNat, HAppend.hAppend, -BitVec.append_eq] using h 21
  · simpa [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_append, Nat.shiftLeft_eq, Sail.BitVec.append', Sail.BitVec.castWidth, BitVec.instHAppendHAddNat, HAppend.hAppend, -BitVec.append_eq] using h 12
#print axioms address
theorem base_value (d : BitVec 64) :
    (S1NextTable10Facts.base d).toNat = (d.extractLsb' 12 36).toNat * 4096 := by
  have h := (d.extractLsb' 12 36).isLt
  simp only [S1NextTable10Facts.base, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
    BitVec.and_zero, BitVec.zero_or, BitVec.toNat_shiftLeft, BitVec.zeroExtend,
    BitVec.toNat_setWidth, Sail.BitVec.extractLsb, BitVec.extractLsb, Nat.shiftLeft_eq, Nat.reduceSub, Nat.reduceAdd, Nat.reducePow]
  omega

theorem base_shape (d : BitVec 64) :
    (S1NextTable10Facts.base d).toNat % 4096 = 0 ∧
      (S1NextTable10Facts.base d).toNat < 2^48 := by
  rw [base_value]
  have h := (d.extractLsb' 12 36).isLt
  omega

theorem stable_extract (d : BitVec 64) :
    (S1Descriptor.stable d).extractLsb' 12 36 = d.extractLsb' 12 36 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  exact S1StablePath.bit_eq _ d (S1ReferenceKind.stable_idempotent d)
    (12 + i) (by omega) (by omega) (by omega)

theorem child_base (wp : S1TTWParams) (d : BitVec 64) :
    (S1NextTable10Facts.base d).setWidth 48 =
      S1LogicalReference.childBase (S1ResourcePath.view wp d) := by
  apply BitVec.eq_of_toNat_eq
  change ((S1NextTable10Facts.base d).setWidth 48).toNat =
    (((S1Descriptor.stable d).extractLsb' 12 36).setWidth 48 <<< 12).toNat
  rw [stable_extract]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, base_value]
  have h := (d.extractLsb' 12 36).isLt
  omega

#print axioms base_value
#print axioms base_shape
#print axioms child_base
theorem next_slot (wp : S1TTWParams) (d va : BitVec 64) (level : Nat) (hl : level < 3) :
    (S1ResourcePath.nextSlot va (level : Int) d).address.toNat =
      S1LogicalReference.entryAddress (S1LogicalReference.childBase (S1ResourcePath.view wp d))
        va (level + 1) 9 := by
  have hs := base_shape d
  have h := address {address := S1NextTable10Facts.base d, paspace := .PAS_NonSecure}
    va (level + 1) (by omega) hs.1 hs.2
  simpa only [S1ResourcePath.nextSlot, Int.natCast_add, Int.natCast_one, child_base wp d] using h
#print axioms next_slot
end S1EntryNextGeometry


