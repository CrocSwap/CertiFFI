import HookQuietCounters.TimerCore
import Lean.Elab.Command
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore ArmFull.SecurityState

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512

namespace HookQuietCounters

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerGuard.security_class_quiet"
  (← IO.getStderr).flush

theorem security_class_quiet (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    (featureValue s .FEAT_RME &&
      ((securityValue s == SS_Root) || (securityValue s == SS_Realm))) =
      ArmCert.HookQuiet.V0.realm s.regs := by
  have hv : featureValue s .FEAT_RME = false ∨
      _get_SCR_EL3_Type_NSE (s.regs.bank_BitVec_64 .SCR_EL3) = 0#1 ∨
      effectiveNSValue s = 1#1 := q.validSecurity
  have hfR : ArmCert.HookQuiet.V0.feature s.regs .FEAT_RME = featureValue s .FEAT_RME := rfl
  have hfS : ArmCert.HookQuiet.V0.feature s.regs .FEAT_SEL2 = featureValue s .FEAT_SEL2 := rfl
  have heff : ArmCert.HookQuiet.V0.effectiveNS s.regs = effectiveNSValue s := rfl
  cases hr : featureValue s .FEAT_RME <;>
    cases hs : featureValue s .FEAT_SEL2 <;>
    rcases bit_cases (_get_SCR_EL3_Type_NSE (s.regs.bank_BitVec_64 .SCR_EL3)) with hnse | hnse <;>
    rcases bit_cases (_get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3)) with hns | hns <;>
    simp_all [securityValue, securityRMEValue, effectiveNSValue, ArmCert.HookQuiet.V0.realm,
      ArmCert.HookQuiet.V0.reg64, BEq.beq, ArmFull.instBEqSecurityState.beq, SecurityState.ctorIdx]

#print axioms security_class_quiet

end HookQuietCounters
