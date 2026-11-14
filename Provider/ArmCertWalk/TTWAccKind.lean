-- The actual TTW access descriptors (descriptor reads: CreateAccDescS1TTW; AF/dirty swaps:
-- CreateAccDescTTEUpdate) carry acctype = TTW, so their events have access kind AK_ttw.
-- Proved from the actual NewAccDesc .AccessType_TTW native result (same observe_simp pattern
-- as canonical S1AccDescFrame.native_frame0/1); no descriptor pin.
import Walk.S1AccDescFrame
import Walk.S1ReadAccDesc
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk

def AccTTW : S1AccDescFrame.Result → Prop
  | .ok a _ => a.acctype = .AccessType_TTW
  | .error _ _ => False

set_option maxRecDepth 1000000 in
theorem native_acc_ttw0 (s : S1AccDescFrame.State) (h : s.regs.PSTATE.EL = 0#2) :
    AccTTW (S2AccDesc.new_native s) := by
  observe_simp [AccTTW, S2AccDesc.new_native]

set_option maxRecDepth 1000000 in
theorem native_acc_ttw1 (s : S1AccDescFrame.State) (h : s.regs.PSTATE.EL = 1#2) :
    AccTTW (S2AccDesc.new_native s) := by
  observe_simp [AccTTW, S2AccDesc.new_native]

theorem new_acc_ttw (s : S1AccDescFrame.State) (out : AccessDescriptor) (t : S1AccDescFrame.State)
    (hEL : s.regs.PSTATE.EL = 0#2 ∨ s.regs.PSTATE.EL = 1#2)
    (hNoRME : s.regs.FeatureImpl[232] = false) (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true) (hNoEL3A32 : s.regs.FeatureImpl[3] = false)
    (call : NewAccDesc .AccessType_TTW s = .ok out t) : out.acctype = .AccessType_TTW := by
  rw [S2AccDesc.new_eq s hNoRME hA64 hEL3A64 hNoEL3A32] at call
  have ttw : AccTTW (S2AccDesc.new_native s) := by
    rcases hEL with h | h
    · exact native_acc_ttw0 s h
    · exact native_acc_ttw1 s h
  rw [call] at ttw
  exact ttw

/-- The descriptor-read base of an actual CreateAccDescS1TTW is a TTW descriptor. -/
theorem read_base_ttw (toplevel : Bool) (varange : VARange) (acc base : AccessDescriptor)
    (s t : S1AccDescFrame.State)
    (hEL : s.regs.PSTATE.EL = 0#2 ∨ s.regs.PSTATE.EL = 1#2)
    (hNoRME : s.regs.FeatureImpl[232] = false) (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true) (hNoEL3A32 : s.regs.FeatureImpl[3] = false)
    (call : CreateAccDescS1TTW toplevel varange acc s = .ok (S1ReadAccDesc.value toplevel varange acc base) t) :
    base.acctype = .AccessType_TTW := by
  obtain ⟨out, t', newCall, _, _, _⟩ := S1AccDescFrame.new_total s hEL hNoRME hA64 hEL3A64 hNoEL3A32
  have actual : CreateAccDescS1TTW toplevel varange acc s = .ok (S1ReadAccDesc.value toplevel varange acc out) t' := by
    simp [CreateAccDescS1TTW, S1ReadAccDesc.value, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, newCall]
  rw [actual] at call
  injection call with values _
  have kinds := congrArg AccessDescriptor.acctype values
  simp only [S1ReadAccDesc.value] at kinds
  rw [← kinds]
  exact new_acc_ttw s out t' hEL hNoRME hA64 hEL3A64 hNoEL3A32 newCall

/-- The swap base of an actual CreateAccDescTTEUpdate is a TTW descriptor. -/
theorem update_base_ttw (acc base : AccessDescriptor) (s t : S1AccDescFrame.State)
    (hEL : s.regs.PSTATE.EL = 0#2 ∨ s.regs.PSTATE.EL = 1#2)
    (hNoRME : s.regs.FeatureImpl[232] = false) (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true) (hNoEL3A32 : s.regs.FeatureImpl[3] = false)
    (call : CreateAccDescTTEUpdate acc s = .ok (S1AccDescFrame.updated acc base) t) :
    base.acctype = .AccessType_TTW := by
  obtain ⟨out, t', newCall, _, _, _⟩ := S1AccDescFrame.new_total s hEL hNoRME hA64 hEL3A64 hNoEL3A32
  have actual : CreateAccDescTTEUpdate acc s = .ok (S1AccDescFrame.updated acc out) t' := by
    simp [CreateAccDescTTEUpdate, S1AccDescFrame.updated, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
      newCall]
  rw [actual] at call
  injection call with values _
  have kinds := congrArg AccessDescriptor.acctype values
  simp only [S1AccDescFrame.updated] at kinds
  rw [← kinds]
  exact new_acc_ttw s out t' hEL hNoRME hA64 hEL3A64 hNoEL3A32 newCall

theorem ttw_access_kind (acc : AccessDescriptor) (ttw : acc.acctype = .AccessType_TTW) :
    AccessDescriptor_to_Access_kind acc = .AK_ttw () := by
  unfold AccessDescriptor_to_Access_kind
  rw [ttw]

#print axioms new_acc_ttw
#print axioms read_base_ttw
#print axioms update_base_ttw
#print axioms ttw_access_kind
end ArmCertWalk
