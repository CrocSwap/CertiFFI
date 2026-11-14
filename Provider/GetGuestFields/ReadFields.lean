import GetGuestFields.View
import GetGuestFields.ControlFacts
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 150000
namespace GetGuestFields.ReadFacts
open S1Normality

def Good (s : State) (v : ActiveView) : EStateM.Result (Sail.Error exception) State S1TTWParams → Prop
  | .ok wp t => Frame s t ∧ active wp = v
  | .error _ _ => False

theorem mair (wp : S1TTWParams) (s : State)
    (hr : s.regs.bank_BitVec_64 .MAIR_EL1 = 0x000000040044ffff#64) :
    Good s {active wp with mair := 0x000000040044ffff#64} (GetGuestFields.mair wp s) := by
  simp [Good, Frame, active, GetGuestFields.mair, Bind.bind, Pure.pure,
    EStateM.bind, EStateM.pure, GetGuestReads.read, hr, Mk_MAIRType]

theorem ps (wp : S1TTWParams) (tcr : BitVec 64) (s : State)
    (hr : s.regs.bank_BitVec_64 .TCR_EL1 = tcr) :
    Good s {active wp with ps := _get_TCR_EL1_Type_IPS tcr} (GetGuestFields.ps wp s) := by
  simp [Good, Frame, active, GetGuestFields.ps, Bind.bind, Pure.pure,
    EStateM.bind, EStateM.pure, GetGuestReads.read, hr]

theorem ds (wp : S1TTWParams) (tcr : BitVec 64) (s : State)
    (hr : s.regs.bank_BitVec_64 .TCR_EL1 = tcr)
    (hz : _get_TCR_EL1_Type_DS tcr = 0#1) :
    Good s {active wp with ds := 0#1} (GetGuestFields.ds wp s) := by
  obtain ⟨feature, hfeat⟩ : ∃ b, GetGuestFeatures.Have52BitIPAAndPASpaceExt.native s = .ok b s := ⟨_, rfl⟩
  cases feature <;>
    by_cases htg : (wp.tgx == .TGx_4KB || wp.tgx == .TGx_16KB) = true <;>
    simp [Good, Frame, active, GetGuestFields.ds, Bind.bind, Pure.pure,
      EStateM.bind, EStateM.pure, GetGuestReads.read, hr, hz, hfeat, htg]
#print axioms mair
#print axioms ps
#print axioms ds
end GetGuestFields.ReadFacts
