import HookQuietCounters.TimerFlow
import Lean.Elab.Command
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512

namespace HookQuietCounters

@[simp] theorem security_query_regs (s : NativeState) :
    (securityQueryState s).regs = s.regs := by unfold securityQueryState; split <;> rfl
@[simp] theorem security_query_mem (s : NativeState) :
    (securityQueryState s).mem = s.mem := by unfold securityQueryState; split <;> rfl
@[simp] theorem security_query_events (s : NativeState) :
    (securityQueryState s).events = s.events := by unfold securityQueryState; split <;> rfl

@[simp] theorem el2_query_regs (s : NativeState) :
    (el2QueryState s).regs = s.regs := by
  unfold el2QueryState secureEL2QueryState
  split <;> first | rfl | (split <;> rfl)
@[simp] theorem el2_query_mem (s : NativeState) :
    (el2QueryState s).mem = s.mem := by
  unfold el2QueryState secureEL2QueryState
  split <;> first | rfl | (split <;> rfl)
@[simp] theorem el2_query_events (s : NativeState) :
    (el2QueryState s).events = s.events := by
  unfold el2QueryState secureEL2QueryState
  split <;> first | rfl | (split <;> rfl)

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerPrepare.ecvGate"
  (← IO.getStderr).flush

def ecvGate (s : NativeState) : Bool :=
  featureValue s .FEAT_ECV &&
    (_get_CNTHCTL_EL2_Type_ECV (s.regs.bank_BitVec_64 .CNTHCTL_EL2) == 1#1) &&
    (_get_SCR_EL3_Type_ECVEn (s.regs.bank_BitVec_64 .SCR_EL3) == 1#1)

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerPrepare.timerPrepareState"
  (← IO.getStderr).flush

def timerPrepareState (s : NativeState) : NativeState :=
  if ecvGate s then el2QueryState (securityQueryState s) else securityQueryState s

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerPrepare.timer_prepare_regs"
  (← IO.getStderr).flush

theorem timer_prepare_regs (s : NativeState) : (timerPrepareState s).regs = s.regs := by
  unfold timerPrepareState
  split <;> simp only [security_query_regs, el2_query_regs]
run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerPrepare.timer_prepare_mem"
  (← IO.getStderr).flush

theorem timer_prepare_mem (s : NativeState) : (timerPrepareState s).mem = s.mem := by
  unfold timerPrepareState
  split <;> simp only [security_query_mem, el2_query_mem]
run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerPrepare.timer_prepare_events"
  (← IO.getStderr).flush

theorem timer_prepare_events (s : NativeState) : (timerPrepareState s).events = s.events := by
  unfold timerPrepareState
  split <;> simp only [security_query_events, el2_query_events]

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerPrepare.timer_preamble"
  (← IO.getStderr).flush

theorem timer_preamble (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ∃ (mask : BitVec 1) (status : Bool), TimerFlow.preamble s =
      .ok (securityValue s, ArmCert.HookQuiet.V0.physicalOffset s.regs, mask, status)
        (timerPrepareState s) := by
  let status := oracleChoiceSource.chooseAt .bool (.site 1174) s.choiceState
  let mask := oracleChoiceSource.chooseAt (.bitvector 1) (.site 1176) s.choiceState
  refine ⟨mask, status, ?_⟩
  have ha : featureValue (securityQueryState s) .FEAT_AA64EL0 = true := by
    unfold featureValue
    rw [security_query_regs]
    exact q.a64
  have hel := el2_enabled (securityQueryState s) ha
  rw [security_query_regs] at hel
  have hf (f : Feature) : featureValue (securityQueryState s) f = featureValue s f := by
    unfold featureValue
    rw [security_query_regs]
  have hQf : ArmCert.HookQuiet.V0.feature s.regs .FEAT_ECV = featureValue s .FEAT_ECV := rfl
  cases hF : featureValue s .FEAT_ECV <;>
    rcases bit_cases (_get_CNTHCTL_EL2_Type_ECV (s.regs.bank_BitVec_64 .CNTHCTL_EL2)) with hC | hC <;>
    rcases bit_cases (_get_SCR_EL3_Type_ECVEn (s.regs.bank_BitVec_64 .SCR_EL3)) with hS | hS <;>
    cases hEL : ArmCert.HookQuiet.V0.el2Enabled s.regs <;>
    simp [TimerFlow.preamble, bind_app, pure_apply, map_apply, ubool, ubv,
      current_security_quiet budget s q, HaveECVExt, feature_apply, read_apply,
      hel, hf, hQf, hF, hC, hS, hEL, timerPrepareState, ecvGate,
      ArmCert.HookQuiet.V0.physicalOffset, ArmCert.HookQuiet.V0.reg64,
      status, mask, Zeros]

#print axioms timer_prepare_regs
#print axioms timer_prepare_mem
#print axioms timer_prepare_events
#print axioms timer_preamble

end HookQuietCounters
