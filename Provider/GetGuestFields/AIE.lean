import GetGuestFields.View
import GetGuestFields.ControlFacts
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace GetGuestFields.AIEFacts
open S1Normality

def Good (input : S1TTWParams) (s : State) : EStateM.Result (Sail.Error exception) State S1TTWParams → Prop
  | .ok wp t => Frame s t ∧ GetGuestFields.active wp = {GetGuestFields.active input with aie := 0#1}
  | .error _ _ => False

theorem good (wp : S1TTWParams) (tcr2 : BitVec 64) (s : State)
    (hr : s.regs.bank_BitVec_64 .TCR2_EL1 = tcr2)
    (hz : s.regs.FeatureImpl[178] = true → _get_TCR2_EL1_Type_AIE tcr2 = 0#1) :
    Good wp s (GetGuestFields.aie wp s) := by
  obtain ⟨feature, hfeat⟩ : ∃ b, GetGuestFeatures.HaveAIEExt.native s = .ok b s := ⟨_, rfl⟩
  cases feature with
  | true =>
    rcases GetGuestFields.ControlFacts.tcr2_total s with ⟨enabled, t, ht, hf, h178⟩
    have hread : GetGuestReads.read ArmFull.Register.TCR2_EL1 t = .ok tcr2 t := by
      change EStateM.Result.ok (t.regs.bank_BitVec_64 .TCR2_EL1) t = .ok tcr2 t
      rw [hf.1, hr]
    cases enabled with
    | false =>
      simp [GetGuestFields.aie, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
        hfeat, ht, Good, GetGuestFields.active, hf]
    | true =>
      have hz' := hz (h178 rfl)
      simp [GetGuestFields.aie, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
        hfeat, ht, hread, Good, GetGuestFields.active, hf, hz']
  | false =>
    simp [GetGuestFields.aie, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
      hfeat, Good, GetGuestFields.active, Frame]
#print axioms good
end GetGuestFields.AIEFacts
