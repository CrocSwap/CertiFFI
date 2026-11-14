import ArmCertWalk.HostDisCH
import ArmCertTranslateModel.HostBinding

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

/-- Internal strengthening of the SAME actual current getter result. -/
theorem host_disch_of_call (state : State) (current : HostRegimeAt state)
    (params : S1TTWParams) (next : State)
    (call : AArch64_S1TTWParamsEL20 .SS_NonSecure .VARange_LOWER state = .ok params next) :
    params.disch = 0#1 := by
  have effect := host_native_disch
    (state.regs.bank_BitVec_64 .TCR_EL2) (state.regs.bank_BitVec_64 .TCR2_EL2)
    (state.regs.bank_BitVec_64 .HCR_EL2) (state.regs.bank_BitVec_64 .SCTLR_EL2)
    (state.regs.bank_BitVec_64 .SCTLR2_EL2) (state.regs.bank_BitVec_64 .SCR_EL3)
    (state.regs.bank_BitVec_64 .MAIR_EL2) (state.regs.bank_BitVec_64 .MAIR2_EL2)
    (state.regs.bank_BitVec_64 .PIR_EL2) (state.regs.bank_BitVec_64 .PIRE0_EL2)
    (state.regs.bank_BitVec_128 ._TTBR0_EL2) (state.regs.bank_BitVec_128 .TTBR1_EL2) state current.d128
  have source := HostLowerSource.complete
    (state.regs.bank_BitVec_64 .TCR_EL2) (state.regs.bank_BitVec_64 .TCR2_EL2)
    (state.regs.bank_BitVec_64 .HCR_EL2) (state.regs.bank_BitVec_64 .SCTLR_EL2)
    (state.regs.bank_BitVec_64 .SCTLR2_EL2) (state.regs.bank_BitVec_64 .SCR_EL3)
    (state.regs.bank_BitVec_64 .MAIR_EL2) (state.regs.bank_BitVec_64 .MAIR2_EL2)
    (state.regs.bank_BitVec_64 .PIR_EL2) (state.regs.bank_BitVec_64 .PIRE0_EL2)
    (state.regs.bank_BitVec_128 ._TTBR0_EL2) (state.regs.bank_BitVec_128 .TTBR1_EL2)
    state current.el3a64 current.noEl3a32 current.noRME current.a64
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    current.tg current.e2h current.d128 current.aie current.pnch current.ds
  rw [← source, call] at effect
  exact effect

theorem host_getter_disch_total (state : State) (current : HostRegimeAt state) :
    ∃ params next,
      AArch64_S1TTWParamsEL20 .SS_NonSecure .VARange_LOWER state = .ok params next ∧
      S1Normality.Frame state next ∧
      HostLower.Shape (state.regs.bank_BitVec_64 .TCR_EL2) (state.regs.bank_BitVec_64 .MAIR_EL2) params ∧
      params.disch = 0#1 := by
  obtain ⟨params, next, call, frame, shape⟩ := host_getter_total state current
  exact ⟨params, next, call, frame, shape, host_disch_of_call state current params next call⟩

#print axioms host_getter_disch_total
end ArmCertWalk
