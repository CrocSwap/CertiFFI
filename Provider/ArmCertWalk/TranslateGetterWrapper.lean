import ArmCertWalk.TranslatePrefixInputs

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

/-- Execute the REAL outer parameter wrapper, including its ignored seed and
all actual occurrence effects. The direct getter equation and intermediate
state are OUTPUT witnesses from that same execution, not entry answers. -/
theorem translate_getter_wrapper_total (va : BitVec 64) (state : State)
    (lower : AArch64_GetVARange va = .VARange_LOWER) (regime : HostRegimeAt state) :
    ∃ params afterSeed other,
      AArch64_GetS1TTWParams .Regime_EL20 .SS_NonSecure va state = .ok params other ∧
      AArch64_S1TTWParamsEL20 .SS_NonSecure .VARange_LOWER afterSeed = .ok params other ∧
      S1Normality.Frame state afterSeed ∧ S1Normality.Frame afterSeed other ∧ S1Normality.Frame state other ∧
      HostLower.Shape (state.regs.bank_BitVec_64 .TCR_EL2) (state.regs.bank_BitVec_64 .MAIR_EL2) params ∧
      HostFlagShape state.regs params ∧ HostAdmissionShape state.regs params ∧ params.disch = 0#1 := by
  obtain ⟨unused, afterSeed, seedCall, seedFrame⟩ := params_draw_normal 1274 state
  have seedRegime : HostRegimeAt afterSeed := regime.of_regs seedFrame.1
  obtain ⟨params, other, directCall, frame, shape, flags, reads⟩ :=
    host_getter_admission_total afterSeed seedRegime
  have disch := host_disch_of_call afterSeed seedRegime params other directCall
  refine ⟨params, afterSeed, other, ?_, directCall, seedFrame, frame,
    S1EntryWP.frame_trans seedFrame frame, ?_, ?_, ?_, disch⟩
  · rw [get_params_el20_eq, ← bind_assoc]
    have lowerCall : AArch64_S1TTWParamsEL20 .SS_NonSecure (AArch64_GetVARange va) afterSeed =
        .ok params other := by rw [lower]; exact directCall
    change (match (do undefined_S1TTWParams (← occLabel 1274) ()) state with
      | .ok _ next => AArch64_S1TTWParamsEL20 .SS_NonSecure (AArch64_GetVARange va) next
      | .error err next => .error err next) = .ok params other
    rw [seedCall]
    exact lowerCall
  · simpa only [seedFrame.1] using shape
  · simpa only [seedFrame.1] using flags
  · simpa only [seedFrame.1] using reads

#print axioms translate_getter_wrapper_total
end ArmCertWalk
