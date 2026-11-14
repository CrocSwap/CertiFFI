import ArmCertWalk.StructuralInputs
import ArmCertWalk.PermissionBitFacts

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

/-- Exact dirty-update condition once the actual permission/alignment checks
have returned Fault_None. The access kind and write flag remain actual data. -/
def leafDirtyEnabled (params : S1TTWParams) (acc : AccessDescriptor) (descriptor : BitVec 64) : Bool :=
  (params.ha == 1#1) && (params.hd == 1#1) &&
    ((params.pie == 1#1) || descriptor.getLsbD 51) && acc.write &&
    !((acc.acctype == .AccessType_AT) || ((acc.acctype == .AccessType_IC) || (acc.acctype == .AccessType_DC)))

def leafUpdateWord (params : S1TTWParams) (acc : AccessDescriptor) (descriptor : BitVec 64) : BitVec 64 :=
  S1Descriptor.hardwareUpdate (params.ha == 1#1) (leafDirtyEnabled params acc descriptor) descriptor

theorem leaf_update_allowed (params : S1TTWParams) (acc : AccessDescriptor) (descriptor : BitVec 64) :
    AllowedUpdate params .leaf descriptor (leafUpdateWord params acc descriptor) := by
  refine ⟨params.ha == 1#1, leafDirtyEnabled params acc descriptor, rfl, ?_, ?_⟩
  · intro enabled
    simpa only [updateAFEnabled, beq_iff_eq] using enabled
  · intro enabled
    simp only [leafDirtyEnabled, Bool.and_eq_true_iff, beq_iff_eq] at enabled
    refine ⟨rfl, enabled.1.1.1.1, enabled.1.1.1.2, ?_⟩
    intro pie
    have either := enabled.1.1.2
    simpa [pie] using either

/-- The source rewrites BOTH halves of its 128-bit scratch descriptor after
an actual 64-bit walk. Its previous undefined contents do not survive. -/
def sourceDescriptor128 (seed : BitVec 128) (descriptor : BitVec 64) : BitVec 128 :=
  Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange seed 63 0 descriptor) 127 64 (Zeros (n := 64))

theorem source_descriptor_128 (seed : BitVec 128) (descriptor : BitVec 64) :
    sourceDescriptor128 seed descriptor = descriptor.setWidth 128 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [sourceDescriptor128, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
    BitVec.zeroExtend, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, Zeros]
  by_cases low : i < 64
  · simp [low, hi]
  · have high : 64 ≤ i := by omega
    have offset : i - 64 < 64 := by omega
    have offsetWide : i - 64 < 128 := by omega
    simp [low, hi, high, offset, offsetWide]

theorem descriptor128_low (descriptor : BitVec 64) :
    Sail.BitVec.extractLsb (descriptor.setWidth 128) 63 0 = descriptor := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have wide : i < 128 := by omega
  simp [Sail.BitVec.extractLsb, BitVec.getLsbD_extractLsb', hi, wide]

theorem descriptor128_injective (first second : BitVec 64)
    (equal : first.setWidth 128 = second.setWidth 128) : first = second := by
  have low := congrArg (fun d : BitVec 128 => Sail.BitVec.extractLsb d 63 0) equal
  simpa only [descriptor128_low] using low

theorem setAF_wide (descriptor : BitVec 64) :
    S1Descriptor.setAF (descriptor.setWidth 128) = (S1Descriptor.setAF descriptor).setWidth 128 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases index : i = 10
  · subst i
    simp [S1Descriptor.setAF, Sail.BitVec.update, Sail.BitVec.updateSubrange', BitVec.zeroExtend]
  · rw [S1Descriptor.setAF_other (descriptor.setWidth 128) i index]
    simp only [BitVec.getLsbD_setWidth, S1Descriptor.setAF_other descriptor i index]

theorem setDirty_wide (descriptor : BitVec 64) :
    S1Descriptor.setDirty (descriptor.setWidth 128) = (S1Descriptor.setDirty descriptor).setWidth 128 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases index : i = 7
  · subst i
    simp [S1Descriptor.setDirty, Sail.BitVec.update, Sail.BitVec.updateSubrange', BitVec.zeroExtend]
  · rw [S1Descriptor.setDirty_other (descriptor.setWidth 128) i index]
    simp only [BitVec.getLsbD_setWidth, S1Descriptor.setDirty_other descriptor i index]

theorem hardware_update_wide (af dirty : Bool) (descriptor : BitVec 64) :
    S1Descriptor.hardwareUpdate af dirty (descriptor.setWidth 128) =
      (S1Descriptor.hardwareUpdate af dirty descriptor).setWidth 128 := by
  cases af <;> cases dirty <;> simp [S1Descriptor.hardwareUpdate, setAF_wide, setDirty_wide]

theorem source_wide_bit51 (descriptor : BitVec 64) :
    (BitVec.setWidth 1 (BitVec.join1 [BitVec.access (descriptor.setWidth 128) 51]) == 1#1) =
      descriptor.getLsbD 51 := by
  simp [Sail.BitVec.join1, Sail.BitVec.access, List.map, BitVec.ofBoolListBE,
    getElem!_pos, ← BitVec.getLsbD_eq_getElem]
  cases descriptor.getLsbD 51 <;> rfl

#print axioms leaf_update_allowed
#print axioms source_descriptor_128
#print axioms descriptor128_low
#print axioms hardware_update_wide
#print axioms source_wide_bit51
end ArmCertWalk
