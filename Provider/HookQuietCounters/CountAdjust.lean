import HookQuietCounters.CountFreeze
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
set_option linter.unusedSimpArgs false
namespace HookQuietCounters

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CountAdjust.security_eq_secure"
  (← IO.getStderr).flush

theorem security_eq_secure (ss : SecurityState) : (ss == SS_Secure) =
    (match ss with | .SS_Secure => true | _ => false) := by cases ss <;> rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CountAdjust.count_adjust_total"
  (← IO.getStderr).flush

set_option maxHeartbeats 200000 in
theorem count_adjust_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat) (ss : SecurityState)
    (resvd enabled frozen prohibited : Bool) :
    ∃ v, CountParts.adjust idx ss resvd enabled frozen prohibited s = .ok v s := by
  by_cases hC : idx = 31
  · cases frozen <;> cases prohibited <;> cases ss <;>
      cases h5 : featureValue s .FEAT_PMUv3p5 <;>
      cases h7 : featureValue s .FEAT_PMUv3p7 <;>
      simp [CountParts.adjust, bind_assoc, bind_if, pure_bind, bind_app,
      CYCLE_COUNTER_ID, HaveEL, have_a64 s q.a64, HavePMUv3p5, HavePMUv3p7,
      feature_apply, h5, h7, read_apply, q.el0, EL0, EL2, EL3,
      hC, security_eq_secure,
      pure_apply, map_apply, if_apply]
  · simp [CountParts.adjust, bind_assoc, bind_if, pure_bind, bind_app,
      CYCLE_COUNTER_ID, HaveEL, have_a64 s q.a64, HavePMUv3p5, HavePMUv3p7,
      feature_apply, read_apply, q.el0, EL0, EL2, EL3,
      hC, security_eq_secure,
      pure_apply, map_apply, if_apply]
#print axioms count_adjust_total
end HookQuietCounters
