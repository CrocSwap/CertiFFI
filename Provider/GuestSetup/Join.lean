import GuestSetup.Recipe
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 150000
namespace GuestSetup.G3
/- Actual initializer followed by finite model writes then actual public Get.
   This proves a nonempty eight-field setup component, not full jointSAT. -/
theorem from_initial_get (oracle : Oracle) (haft pie e0poe : Bool)
    (ss : SecurityState) (va : BitVec 64) :
    ∃ (initial setup final : State) (wp : S1TTWParams),
      ArmFull.initialState oracle = .ok () initial ∧
      install tcr (tcr2 haft pie e0poe) initial = .ok () setup ∧
      setup.regs.bank_Bool .__tlb_enabled = false ∧
      AArch64_GetS1TTWParams .Regime_EL10 ss va setup = .ok wp final ∧
      S1Normality.Frame setup final ∧
      GetGuestFields.active wp = GetGuestFields.Shape.expected 16#6 5#3 ∧
      setup.mem = initial.mem ∧ setup.events = initial.events ∧
      setup.choiceState = initial.choiceState ∧ setup.choiceOcc = initial.choiceOcc := by
  rcases InitTLBFrame.initial_total oracle with ⟨initial, hi, ht⟩
  let setup := after tcr (tcr2 haft pie e0poe) initial
  have hr := raw tcr (tcr2 haft pie e0poe) initial (guards haft pie e0poe)
  rcases GetGuestFields.Dispatch.shape tcr (setup.regs.bank_BitVec_64 .TCR2_EL1)
    ss va setup hr (granule _) with ⟨wp, final, hg, hf, hv⟩
  rw [txsz, ips] at hv
  refine ⟨initial, setup, final, wp, hi, install_run _ _ _, ?_, hg, hf, hv, ?_⟩
  · exact (after_tlb _ _ _).trans ht
  · exact after_frame _ _ _
#print axioms from_initial_get
end GuestSetup.G3
