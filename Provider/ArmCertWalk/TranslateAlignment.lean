import ArmCertWalk.PermissionCheckTotal
import ArmCertTranslateModel.GuardedPageFrame

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

def fetchGuardRegs (acc : AccessDescriptor) (next : TTWState) (regs : Regs) : Regs :=
  if acc.acctype == .AccessType_IFETCH then gpRegs regs (next.guardedpage == 1#1) else regs

def fetchGuardState (acc : AccessDescriptor) (next : TTWState) (state : State) : State :=
  {state with regs := fetchGuardRegs acc next state.regs}

theorem fetch_guard_call (acc : AccessDescriptor) (next : TTWState) (state : State) :
    (if acc.acctype == .AccessType_IFETCH then SetInGuardedPage (next.guardedpage == 1#1)
      else (pure () : SailM Unit)) state = .ok () (fetchGuardState acc next state) := by
  by_cases fetch : acc.acctype == .AccessType_IFETCH
  · simp only [fetch, ↓reduceIte, fetchGuardState, fetchGuardRegs]
    exact set_guarded_page _ _
  · simp only [fetch, ↓reduceIte, fetchGuardState, fetchGuardRegs]
    rfl

theorem computed_controls_fetch_guard (permissions : Permissions) (params : S1TTWParams)
    (acc : AccessDescriptor) (next : TTWState) (regs : Regs) :
    computedControls permissions params (fetchGuardRegs acc next regs) = computedControls permissions params regs := by
  unfold fetchGuardRegs
  split <;> rfl

/-- Normal memory has no source alignment fault for ANY actual aligned/tag/
MTE/a32lsmd values. The MTE feature query is retained; it is not pinned off. -/
theorem normal_alignment_false (acc : AccessDescriptor) (aligned : Bool) (ntlsmd : BitVec 1)
    (attrs : MemoryAttributes) (state : State) (normal : attrs.memtype = .MemType_Normal) :
    AArch64_S1HasAlignmentFault acc aligned ntlsmd attrs state = .ok false state := by
  have mte : ∃ value, HaveMTEExt () state = .ok value state := ⟨_, rfl⟩
  obtain ⟨mte, mteCall⟩ := mte
  have notDevice : ((.MemType_Normal : MemType) == .MemType_Device) = false := rfl
  by_cases fetch : acc.acctype == .AccessType_IFETCH
  all_goals
    simp [AArch64_S1HasAlignmentFault, fetch, mteCall, normal, notDevice,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]

#print axioms fetch_guard_call
#print axioms computed_controls_fetch_guard
#print axioms normal_alignment_false
end ArmCertWalk
