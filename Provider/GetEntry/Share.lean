import GetEntry.WP
import Walk.S1EL10PermsCallees
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 150000
namespace S1EntryShare
open S1Normality

def action {R : Type} (regime : Regime) : SailME R Bool :=
  if (regime == .Regime_EL10) then do
    let enabled ← EL2Enabled ()
    if enabled then do
      let vm ← do
        let hcr ← readReg ArmFull.Register.HCR_EL2
        pure (_get_HCR_EL2_Type_VM hcr == 1#1)
      if vm then do
        let choice ← __IMPDEF_boolean "Apply effective shareability at stage 1"
        pure (!choice)
      else pure false
    else pure false
  else pure false

theorem disabled {R : Type} (regime : Regime) (s : State)
    (hVM : _get_HCR_EL2_Type_VM (s.regs.bank_BitVec_64 .HCR_EL2) = 0#1) :
    ∃ t, (action regime : SailME R Bool) s = .ok (.ok false) t ∧ Frame s t := by
  by_cases hreg : (regime == .Regime_EL10) = true
  · rcases S1EL10PermsCallees.el2_normal s with ⟨enabled, t, hr, hf⟩
    have hv : _get_HCR_EL2_Type_VM (t.regs.bank_BitVec_64 .HCR_EL2) = 0#1 := by
      rw [hf.1]; exact hVM
    have hread : (readReg ArmFull.Register.HCR_EL2 : SailM (BitVec 64)) t =
        .ok (t.regs.bank_BitVec_64 .HCR_EL2) t := rfl
    refine ⟨t, ?_, hf⟩
    cases enabled <;>
      simp [action, hreg, Bind.bind, Pure.pure, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
        liftM, monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.pure, Functor.map, EStateM.map,
        EStateM.bind, EStateM.pure, hr, hread, hv]
  · refine ⟨s, ?_, rfl, rfl, rfl⟩
    simp [action, hreg, Pure.pure, ExceptT.pure, ExceptT.mk, EStateM.pure]

theorem bind_disabled {R α : Type} (regime : Regime) (k : Bool → SailME R α)
    (s : State) (next : α → State → Prop) (exit : R → State → Prop)
    (hVM : _get_HCR_EL2_Type_VM (s.regs.bank_BitVec_64 .HCR_EL2) = 0#1)
    (hk : ∀ t, Frame s t → S1EntryWP.WP (k false) t next exit) :
    S1EntryWP.WP (action regime >>= k) s next exit := by
  rcases disabled (R := R) regime s hVM with ⟨t, hr, hf⟩
  apply S1EntryWP.bind_wp
  exact ⟨.ok false, t, hr, hk t hf⟩
#print axioms disabled
#print axioms bind_disabled
end S1EntryShare
