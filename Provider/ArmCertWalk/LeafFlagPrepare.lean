import ArmCertWalk.TranslateUpdateSource
import ArmCertWalk.LeafUpdateData

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

def leafDirtyWide (params : S1TTWParams) (acc : AccessDescriptor) (descriptor : BitVec 128) : Bool :=
  (params.ha == 1#1) && (params.hd == 1#1) &&
    ((params.pie == 1#1) || (BitVec.setWidth 1 (BitVec.join1 [BitVec.access descriptor 51]) == 1#1)) && acc.write &&
    !((acc.acctype == .AccessType_AT) || ((acc.acctype == .AccessType_IC) || (acc.acctype == .AccessType_DC)))

def leafWordWide (params : S1TTWParams) (acc : AccessDescriptor) (descriptor : BitVec 128) : BitVec 128 :=
  S1Descriptor.hardwareUpdate (params.ha == 1#1) (leafDirtyWide params acc descriptor) descriptor

theorem leaf_word_wide_eq (params : S1TTWParams) (acc : AccessDescriptor) (descriptor : BitVec 64) :
    leafWordWide params acc (descriptor.setWidth 128) = (leafUpdateWord params acc descriptor).setWidth 128 := by
  simp only [leafWordWide, leafDirtyWide, source_wide_bit51]
  exact hardware_update_wide _ _ _

theorem leaf_flag_prepare_wide (params : S1TTWParams) (acc : AccessDescriptor)
    (descriptor : BitVec 128) (fault : FaultRecord) (state : State)
    (noFault : fault.statuscode = .Fault_None) :
    TranslateUpdateSource.prepare params acc descriptor fault state =
      .ok (.ok (leafWordWide params acc descriptor)) state := by
  have accessPerm : AArch64_SettingAccessFlagPermitted fault = (pure true : SailM Bool) := by
    unfold AArch64_SettingAccessFlagPermitted
    rw [noFault]
    rfl
  have dirtyPerm : AArch64_SettingDirtyStatePermitted fault = (pure true : SailM Bool) := by
    unfold AArch64_SettingDirtyStatePermitted
    rw [noFault]
    rfl
  have one : Bit (1#1) = 1#1 := by decide
  have zero : Bit (0#1) = 0#1 := by decide
  by_cases af : params.ha == 1#1
  all_goals
    simp only [TranslateUpdateSource.prepare, accessPerm, dirtyPerm,
      leafWordWide, leafDirtyWide, S1Descriptor.hardwareUpdate, S1Descriptor.setAF,
      S1Descriptor.setDirty, af, one, zero, Bool.true_and, Bool.false_and,
      ↓reduceIte, pure_bind, bind_pure_comp]
    rfl

theorem leaf_flag_prepare_total (params : S1TTWParams) (acc : AccessDescriptor)
    (descriptor : BitVec 64) (fault : FaultRecord) (state : State)
    (noFault : fault.statuscode = .Fault_None) :
    TranslateUpdateSource.prepare params acc (descriptor.setWidth 128) fault state =
      .ok (.ok ((leafUpdateWord params acc descriptor).setWidth 128)) state := by
  simpa only [leaf_word_wide_eq] using leaf_flag_prepare_wide params acc (descriptor.setWidth 128) fault state noFault

#print axioms leaf_word_wide_eq
#print axioms leaf_flag_prepare_wide
#print axioms leaf_flag_prepare_total
end ArmCertWalk
