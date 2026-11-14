import NativeMteTagCheck.Primitive
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option Elab.async false

namespace NativeMteTagCheck
open S1Normality MemM1.NoFault

def allocationAfter (s : State) : State :=
  advanceOcc 1355 (advanceOcc 1354 (advanceOcc 1357 (advanceOcc 1356 s)))

theorem allocation_tag_exact (descriptor : AddressDescriptor) (access : AccessDescriptor)
    (physicalTag : BitVec 4) (s : State)
    (kind : descriptor.memattrs.tags = .MemTag_AllocationTagged) (allowed : TagStatusOK s) :
    ∃ matched t, AArch64_AllocationTagCheck descriptor access physicalTag s = .ok matched t ∧
      Frame s t ∧ t = allocationAfter s := by
  let first := advanceOcc 1356 s
  let statusLabel := ChoiceLabel.occ 1356 (s.choiceOcc.getD 1356 0)
  obtain ⟨unusedStatus, hs⟩ := phys_status_total statusLabel first
  let beforeRead := advanceOcc 1357 first
  let tagLabel := ChoiceLabel.occ 1357 (first.choiceOcc.getD 1357 0)
  obtain ⟨unusedTag, ht⟩ := S1Unknowns.bits_at_total 4 tagLabel beforeRead
  have allowedRead : TagStatusOK beforeRead :=
    tag_status_advance 1357 first (by decide) (tag_status_advance 1356 s (by decide) allowed)
  obtain ⟨status, tag, read, noFault, readFrame⟩ :=
    phys_tag_read_no_fault descriptor access beforeRead allowedRead
  have sameKind : (MemTagType.MemTag_AllocationTagged == MemTagType.MemTag_AllocationTagged) = true := rfl
  refine ⟨physicalTag == tag, _, ?_,
    frame_trans (frame_trans (advance_frame 1356 s) (advance_frame 1357 first)) readFrame, rfl⟩
  simp only [AArch64_AllocationTagCheck, occurrence, hs, ht, kind, sameKind, read, noFault,
    first, beforeRead, statusLabel, tagLabel, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
    Bool.false_eq_true, ite_false, ite_true]
  all_goals rfl

theorem allocation_tag_frame (descriptor : AddressDescriptor) (access : AccessDescriptor)
    (physicalTag : BitVec 4) (s : State)
    (kind : descriptor.memattrs.tags = .MemTag_AllocationTagged) (allowed : TagStatusOK s) :
    ∃ matched t, AArch64_AllocationTagCheck descriptor access physicalTag s = .ok matched t ∧
      Frame s t := by
  obtain ⟨matched, t, run, frame, _⟩ :=
    allocation_tag_exact descriptor access physicalTag s kind allowed
  exact ⟨matched, t, run, frame⟩

theorem allocation_choice_delta (s : State) : ChoiceDelta s (allocationAfter s) 1 := by
  simp [ChoiceDelta, allocationAfter, advanceOcc, Std.ExtHashMap.getD_insert]

theorem allocation_tag_transport (descriptor : AddressDescriptor) (access : AccessDescriptor)
    (physicalTag : BitVec 4) (s : State)
    (kind : descriptor.memattrs.tags = .MemTag_AllocationTagged) (allowed : TagStatusOK s) :
    ∃ matched t, AArch64_AllocationTagCheck descriptor access physicalTag s = .ok matched t ∧
      Frame s t ∧ ChoiceDelta s t 1 := by
  obtain ⟨matched, t, run, frame, exactState⟩ :=
    allocation_tag_exact descriptor access physicalTag s kind allowed
  exact ⟨matched, t, run, frame, exactState.symm ▸ allocation_choice_delta s⟩

theorem check_tag_frame (descriptor : AddressDescriptor) (access : AccessDescriptor)
    (physicalTag : BitVec 4) (s : State)
    (allowed : descriptor.memattrs.tags = .MemTag_AllocationTagged → TagStatusOK s) :
    ∃ matched t, AArch64_CheckTag descriptor access physicalTag s = .ok matched t ∧ Frame s t := by
  cases kind : descriptor.memattrs.tags with
  | MemTag_Untagged =>
    refine ⟨true, s, ?_, rfl, rfl, rfl⟩
    simp only [AArch64_CheckTag, kind]
    all_goals rfl
  | MemTag_CanonicallyTagged =>
    refine ⟨AArch64_CanonicalTagCheck descriptor physicalTag, s, ?_, rfl, rfl, rfl⟩
    simp only [AArch64_CheckTag, kind]
    all_goals rfl
  | MemTag_AllocationTagged =>
    obtain ⟨matched, t, run, frame⟩ := allocation_tag_frame descriptor access physicalTag s kind (allowed kind)
    have sameKind : (MemTagType.MemTag_AllocationTagged == MemTagType.MemTag_AllocationTagged) = true := rfl
    refine ⟨matched, t, ?_, frame⟩
    simpa only [AArch64_CheckTag, kind, sameKind, ite_true] using run

/-- This block occurs after translation in both actual MemSingle read and set. -/
def checkedAccess (address : BitVec 64) (descriptor : AddressDescriptor)
    (access : AccessDescriptor) : SailM Unit := do
  let mte ← HaveMTE2Ext ()
  if mte && access.tagchecked then
    let matched ← AArch64_CheckTag descriptor access (AArch64_PhysicalTag address)
    if !matched then AArch64_TagCheckFault address access else pure ()
  else pure ()

/-- exact-branch facts for FEAT_MTE2 absent (FeatureImpl[134] = false). -/
theorem mte2_off (s : State) (h : s.regs.FeatureImpl[134]! = false) :
    (HaveMTE2Ext () : SailM Bool) s = .ok false s := (NativeMte2.have_mte2 s).trans (by rw [h])
theorem mte2_on (s : State) (h : s.regs.FeatureImpl[134]! = true) :
    (HaveMTE2Ext () : SailM Bool) s = .ok true s := (NativeMte2.have_mte2 s).trans (by rw [h])
theorem checked_off (address : BitVec 64) (descriptor : AddressDescriptor) (access : AccessDescriptor)
    (s : State) (h : s.regs.FeatureImpl[134]! = false) :
    checkedAccess address descriptor access s = .ok () s := by
  simp only [checkedAccess, NativeMte2.have_mte2, h, Bool.false_and, Bind.bind, EStateM.bind,
    Pure.pure, EStateM.pure, Bool.false_eq_true, ite_false]

theorem tagcheck_no_abort (catalogue : ControlCatalogue) (address : BitVec 64)
    (descriptor : AddressDescriptor) (access : AccessDescriptor) (s : State)
    (controls : DefaultAt catalogue s) (el : access.el = EL0)
    (allowed : access.tagchecked = true →
      descriptor.memattrs.tags = .MemTag_AllocationTagged → TagStatusOK s) :
    ∃ t, checkedAccess address descriptor access s = .ok () t ∧
      Frame s t ∧ DefaultAt catalogue t := by
  cases hm : s.regs.FeatureImpl[134]! with
  | false => exact ⟨s, checked_off address descriptor access s hm, ⟨rfl, rfl, rfl⟩, controls⟩
  | true =>
    cases tagchecked : access.tagchecked with
    | false =>
      refine ⟨s, ?_, ⟨rfl, rfl, rfl⟩, controls⟩
      simp only [checkedAccess, NativeMte2.have_mte2, hm, tagchecked,
        Bool.and_false, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
      all_goals rfl
    | true =>
      obtain ⟨matched, afterCheck, checked, checkFrame⟩ :=
        check_tag_frame descriptor access (AArch64_PhysicalTag address) s (allowed tagchecked)
      cases matched with
      | true =>
        refine ⟨afterCheck, ?_, checkFrame, controls.transport checkFrame⟩
        simp only [checkedAccess, NativeMte2.have_mte2, hm, tagchecked, checked,
          Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
          Bool.true_and, Bool.and_true, Bool.not_true, Bool.not_false,
          Bool.false_eq_true, ite_true, ite_false]
        all_goals rfl
      | false =>
        have afterControls := controls.transport checkFrame
        obtain ⟨t, fault, faultFrame⟩ :=
          NativeMte2.tcf0_fault_no_report address access afterCheck afterControls.host el afterControls.tcf0
        have frame := frame_trans checkFrame faultFrame
        refine ⟨t, ?_, frame, controls.transport frame⟩
        simp only [checkedAccess, NativeMte2.have_mte2, hm, tagchecked, checked, fault,
          Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
          Bool.true_and, Bool.and_true, Bool.not_true, Bool.not_false,
          Bool.false_eq_true, ite_true, ite_false]
        all_goals rfl

#print axioms allocation_tag_frame
#print axioms allocation_tag_exact
#print axioms allocation_tag_transport
#print axioms check_tag_frame
#print axioms tagcheck_no_abort
end NativeMteTagCheck
