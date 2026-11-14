import GetGuestFields.View
import GetGuestFields.ControlFacts
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace GetGuestFields.PnCHFacts
open S1Normality

def Good (input : S1TTWParams) (s : State) : EStateM.Result (Sail.Error exception) State S1TTWParams → Prop
  | .ok wp t => Frame s t ∧ active wp = {active input with pnch := 0#1}
  | .error _ _ => False

theorem good (wp : S1TTWParams) (tcr2 : BitVec 64) (s : State)
    (hr : s.regs.bank_BitVec_64 .TCR2_EL1 = tcr2)
    (hz : s.regs.FeatureImpl[178] = true → _get_TCR2_EL1_Type_PnCH tcr2 = 0#1) :
    Good wp s (GetGuestFields.pnch wp s) := by
  obtain ⟨feature, hfeat⟩ : ∃ b, GetGuestFeatures.HaveTHExt.native s = .ok b s := ⟨_, rfl⟩
  cases feature with
  | false =>
    simp [GetGuestFields.pnch, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
      hfeat, Good, active, Frame]
  | true =>
    by_cases hd : wp.d128 = 0#1
    · rcases ControlFacts.tcr2_total s with ⟨enabled, t, ht, hf, h178⟩
      have hread : GetGuestReads.read ArmFull.Register.TCR2_EL1 t = .ok tcr2 t := by
        change EStateM.Result.ok (t.regs.bank_BitVec_64 .TCR2_EL1) t = .ok tcr2 t
        rw [hf.1, hr]
      cases enabled with
      | false =>
        simp [GetGuestFields.pnch, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
          hfeat, hd, ht, Good, active, hf]
      | true =>
        have hz' := hz (h178 rfl)
        simp [GetGuestFields.pnch, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
          hfeat, hd, ht, hread, Good, active, hf, hz']
    · simp [GetGuestFields.pnch, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
        hfeat, hd, Good, active, Frame]
#print axioms good
end GetGuestFields.PnCHFacts
