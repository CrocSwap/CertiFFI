import ArmCertWalk.HostLower
import ArmCertTranslateModel.TopologyImage
import ArmCertTranslateModel.GuardedPageFrame

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

/-- CURRENT primitive conditions of the frozen lower-host parameter getter.
    No register word, inactive MAIR2/PIR value, future result or frame law is
    fixed here. This is a getter binding component, not full access admission. -/
structure HostRegimeAt (state : State) : Prop where
  el3a64 : state.regs.FeatureImpl[7] = true
  noEl3a32 : state.regs.FeatureImpl[3] = false
  noRME : state.regs.FeatureImpl[232] = false
  a64 : state.regs.PSTATE.nRW = 0#1
  tg : _get_TCR_EL2_Type_TG0 (state.regs.bank_BitVec_64 .TCR_EL2) = 0#2
  e2h : _get_HCR_EL2_Type_E2H (state.regs.bank_BitVec_64 .HCR_EL2) = 1#1
  d128 : state.regs.FeatureImpl[178] = true →
    _get_TCR2_EL2_Type_D128 (state.regs.bank_BitVec_64 .TCR2_EL2) = 0#1
  aie : state.regs.FeatureImpl[178] = true →
    _get_TCR2_EL2_Type_AIE (state.regs.bank_BitVec_64 .TCR2_EL2) = 0#1
  pnch : state.regs.FeatureImpl[178] = true →
    _get_TCR2_EL2_Type_PnCH (state.regs.bank_BitVec_64 .TCR2_EL2) = 0#1
  ds : BitVec.slice (state.regs.bank_BitVec_64 .TCR_EL2) 59 1 = 0#1

/-- The actual native getter result is DERIVED. All opaque/inactive whole-word
    arguments are the actual current reads, not additional environment pins. -/
theorem host_getter_total (state : State) (current : HostRegimeAt state) :
    ∃ params next,
      AArch64_S1TTWParamsEL20 .SS_NonSecure .VARange_LOWER state = .ok params next ∧
      S1Normality.Frame state next ∧
      HostLower.Shape (state.regs.bank_BitVec_64 .TCR_EL2)
        (state.regs.bank_BitVec_64 .MAIR_EL2) params := by
  exact HostLower.total
    (state.regs.bank_BitVec_64 .TCR_EL2) (state.regs.bank_BitVec_64 .TCR2_EL2)
    (state.regs.bank_BitVec_64 .HCR_EL2) (state.regs.bank_BitVec_64 .SCTLR_EL2)
    (state.regs.bank_BitVec_64 .SCTLR2_EL2) (state.regs.bank_BitVec_64 .SCR_EL3)
    (state.regs.bank_BitVec_64 .MAIR_EL2) (state.regs.bank_BitVec_64 .MAIR2_EL2)
    (state.regs.bank_BitVec_64 .PIR_EL2) (state.regs.bank_BitVec_64 .PIRE0_EL2)
    (state.regs.bank_BitVec_128 ._TTBR0_EL2) (state.regs.bank_BitVec_128 .TTBR1_EL2)
    state current.el3a64 current.noEl3a32 current.noRME current.a64
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    current.tg current.e2h current.d128 current.aie current.pnch current.ds

theorem HostRegimeAt.of_regs {state other : State} (h : HostRegimeAt state)
    (registers : other.regs = state.regs) : HostRegimeAt other := by
  exact ⟨by rw [registers]; exact h.el3a64, by rw [registers]; exact h.noEl3a32,
    by rw [registers]; exact h.noRME, by rw [registers]; exact h.a64,
    by rw [registers]; exact h.tg, by rw [registers]; exact h.e2h,
    by rw [registers]; exact h.d128, by rw [registers]; exact h.aie,
    by rw [registers]; exact h.pnch, by rw [registers]; exact h.ds⟩

theorem HostRegimeAt.guarded_page (state : State) (h : HostRegimeAt state) (guarded : Bool) :
    HostRegimeAt {state with regs := gpRegs state.regs guarded} :=
  ⟨h.el3a64, h.noEl3a32, h.noRME, h.a64, h.tg, h.e2h, h.d128, h.aie, h.pnch, h.ds⟩

/-- The actual getter leaves the current image AND its own primitive binding
    available at the same successor; real oracle occurrence changes are kept. -/
theorem host_getter_preserves_image {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (state : State)
    (current : HostRegimeAt state) (image : TopologyImageAt spec state) :
    ∃ params next,
      AArch64_S1TTWParamsEL20 .SS_NonSecure .VARange_LOWER state = .ok params next ∧
      S1Normality.Frame state next ∧ HostRegimeAt next ∧ TopologyImageAt spec next ∧
      HostLower.Shape (state.regs.bank_BitVec_64 .TCR_EL2)
        (state.regs.bank_BitVec_64 .MAIR_EL2) params := by
  obtain ⟨params, next, heq, hframe, hshape⟩ := host_getter_total state current
  refine ⟨params, next, heq, hframe, current.of_regs hframe.1, ?_, hshape⟩
  unfold TopologyImageAt
  rw [hframe.2.1]
  exact image

#print axioms host_getter_total
#print axioms HostRegimeAt.of_regs
#print axioms HostRegimeAt.guarded_page
#print axioms host_getter_preserves_image
end ArmCert.Translate.Model
