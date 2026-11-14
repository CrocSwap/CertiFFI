import HookQuietCounters.EventParts
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
set_option linter.unusedSimpArgs false
namespace HookQuietCounters

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventPrepare.EventRange"
  (← IO.getStderr).flush

def EventRange (p : Option (Int × (BitVec 64))) : Prop :=
  match p with
  | none => True
  | some (n, _) => ((0 ≤b n) && (n <b 64)) = true

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventPrepare.eventIndex"
  (← IO.getStderr).flush

def eventIndex (i : BitVec 4) (high : Bool) : Int :=
  if high then (i.toNat : Int)+8 else (i.toNat : Int)

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventPrepare.event_range_index"
  (← IO.getStderr).flush

theorem event_range_index (i : BitVec 4) (high : Bool) (offset : BitVec 64) :
    EventRange (some (eventIndex i high, offset)) := by
  have h := event_index_range i high
  cases high <;> simpa only [EventRange, eventIndex, Bool.false_eq_true, reduceIte, Int.add_zero] using h

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventPrepare.eventPEnabled"
  (← IO.getStderr).flush

def eventPEnabled (s : NativeState) : Bool :=
  _get_CNTHCTL_EL2_Type_EVNTEN (s.regs.bank_BitVec_64 .CNTHCTL_EL2) == 1#1

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventPrepare.eventPState"
  (← IO.getStderr).flush

def eventPState (s : NativeState) : NativeState :=
  if eventPEnabled s && featureValue s .FEAT_ECV then el2QueryState s else s

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventPrepare.eventPValue"
  (← IO.getStderr).flush

def eventPValue (s : NativeState) : Option (Int × (BitVec 64)) :=
  if eventPEnabled s then
    let n := eventIndex (_get_CNTHCTL_EL2_Type_EVNTI (s.regs.bank_BitVec_64 .CNTHCTL_EL2))
      (featureValue s .FEAT_ECV && (_get_CNTHCTL_EL2_Type_EVNTIS (s.regs.bank_BitVec_64 .CNTHCTL_EL2) == 1#1))
    let offset := if featureValue s .FEAT_ECV then
      if ArmCert.HookQuiet.V0.el2Enabled s.regs &&
        (_get_CNTHCTL_EL2_Type_ECV (s.regs.bank_BitVec_64 .CNTHCTL_EL2) == 1#1) &&
        (_get_SCR_EL3_Type_ECVEn (s.regs.bank_BitVec_64 .SCR_EL3) == 1#1)
      then s.regs.bank_BitVec_64 .CNTPOFF_EL2 else 0#64
    else oracleChoiceSource.chooseAt (.bitvector 64) (.site 1180) s.choiceState
    some (n, offset)
  else none

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventPrepare.event_prepare_p_eq"
  (← IO.getStderr).flush

theorem event_prepare_p_eq (s : NativeState) (ha : featureValue s .FEAT_AA64EL0 = true) :
    EventParts.prepareP s = .ok (eventPValue s) (eventPState s) := by
  rcases uint (.site 1179) s with ⟨n, hn⟩
  have hel := el2_enabled s ha
  cases hF : featureValue s .FEAT_ECV <;>
    rcases bit_cases (_get_CNTHCTL_EL2_Type_EVNTEN (s.regs.bank_BitVec_64 .CNTHCTL_EL2)) with hEN | hEN <;>
    rcases bit_cases (_get_CNTHCTL_EL2_Type_EVNTIS (s.regs.bank_BitVec_64 .CNTHCTL_EL2)) with hIS | hIS <;>
    cases hEL : ArmCert.HookQuiet.V0.el2Enabled s.regs <;>
    rcases bit_cases (_get_CNTHCTL_EL2_Type_ECV (s.regs.bank_BitVec_64 .CNTHCTL_EL2)) with hC | hC <;>
    rcases bit_cases (_get_SCR_EL3_Type_ECVEn (s.regs.bank_BitVec_64 .SCR_EL3)) with hS | hS <;>
    simp [EventParts.prepareP, bind_app, pure_apply, map_apply, hn, ubv,
      read_apply, HaveECVExt, feature_apply, hF, hEN, hIS, hEL, hC, hS,
      hel, el2_query_regs, eventPValue, eventPState, eventPEnabled, eventIndex, Zeros]

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventPrepare.event_p_range"
  (← IO.getStderr).flush

theorem event_p_range (s : NativeState) : EventRange (eventPValue s) := by
  unfold eventPValue
  by_cases he : eventPEnabled s = true
  · rw [if_pos he]
    exact event_range_index _ _ _
  · rw [if_neg he]
    trivial

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventPrepare.event_p_frame"
  (← IO.getStderr).flush

theorem event_p_frame (s : NativeState) : TimerFrame s (eventPState s) := by
  unfold eventPState
  split
  · exact TimerFrame.of_eraseOcc_eq (erase_el2_query s)
  · exact TimerFrame.refl s

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventPrepare.event_prepare_p"
  (← IO.getStderr).flush

theorem event_prepare_p (s : NativeState) (ha : featureValue s .FEAT_AA64EL0 = true) :
    ∃ p t, EventParts.prepareP s = .ok p t ∧ TimerFrame s t ∧ EventRange p :=
  ⟨eventPValue s, eventPState s, event_prepare_p_eq s ha, event_p_frame s, event_p_range s⟩
#print axioms event_prepare_p

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventPrepare.eventVHost"
  (← IO.getStderr).flush

def eventVHost (s : NativeState) : Bool :=
  ((_get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2)) +++
    (_get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2))) == 3#2

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventPrepare.eventVEnabled"
  (← IO.getStderr).flush

def eventVEnabled (s : NativeState) : Bool :=
  !(featureValue s .FEAT_VHE && eventVHost s) &&
    (_get_CNTKCTL_EL1_Type_EVNTEN (s.regs.bank_BitVec_64 .CNTKCTL_EL1) == 1#1)

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventPrepare.eventVState"
  (← IO.getStderr).flush

def eventVState (s : NativeState) : NativeState :=
  if eventVEnabled s then el2QueryState s else s

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventPrepare.eventVValue"
  (← IO.getStderr).flush

def eventVValue (s : NativeState) : Option (Int × (BitVec 64)) :=
  if eventVEnabled s then
    let n := eventIndex (_get_CNTKCTL_EL1_Type_EVNTI (s.regs.bank_BitVec_64 .CNTKCTL_EL1))
      (featureValue s .FEAT_ECV && (_get_CNTKCTL_EL1_Type_EVNTIS (s.regs.bank_BitVec_64 .CNTKCTL_EL1) == 1#1))
    let offset := if !(ArmCert.HookQuiet.V0.el2Enabled s.regs) || !(eventVHost s)
      then s.regs.bank_BitVec_64 .CNTVOFF_EL2 else 0#64
    some (n, offset)
  else none

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventPrepare.event_prepare_v_eq"
  (← IO.getStderr).flush

theorem event_prepare_v_eq (s : NativeState) (ha : featureValue s .FEAT_AA64EL0 = true) :
    EventParts.prepareV s = .ok (eventVValue s) (eventVState s) := by
  rcases uint (.site 1184) s with ⟨n, hn⟩
  have hel := el2_enabled s ha
  cases hF : featureValue s .FEAT_ECV <;>
    cases hVH : featureValue s .FEAT_VHE <;>
    by_cases hHost : ((_get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2)) +++
      (_get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2))) = 3#2 <;>
    rcases bit_cases (_get_CNTKCTL_EL1_Type_EVNTEN (s.regs.bank_BitVec_64 .CNTKCTL_EL1)) with hEN | hEN <;>
    rcases bit_cases (_get_CNTKCTL_EL1_Type_EVNTIS (s.regs.bank_BitVec_64 .CNTKCTL_EL1)) with hIS | hIS <;>
    cases hEL : ArmCert.HookQuiet.V0.el2Enabled s.regs <;>
    simp [EventParts.prepareV, bind_app, pure_apply, map_apply, hn, ubv,
      read_apply, HaveECVExt, HaveVirtHostExt, HaveEL, feature_apply, hF, hVH, hHost, hEN, hIS, hEL,
      hel, el2_query_regs, eventVValue, eventVState, eventVEnabled, eventVHost, eventIndex, Zeros]

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventPrepare.event_v_range"
  (← IO.getStderr).flush

theorem event_v_range (s : NativeState) : EventRange (eventVValue s) := by
  unfold eventVValue
  by_cases he : eventVEnabled s = true
  · rw [if_pos he]
    exact event_range_index _ _ _
  · rw [if_neg he]
    trivial

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventPrepare.event_v_frame"
  (← IO.getStderr).flush

theorem event_v_frame (s : NativeState) : TimerFrame s (eventVState s) := by
  unfold eventVState
  split
  · exact TimerFrame.of_eraseOcc_eq (erase_el2_query s)
  · exact TimerFrame.refl s

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventPrepare.event_prepare_v"
  (← IO.getStderr).flush

theorem event_prepare_v (s : NativeState) (ha : featureValue s .FEAT_AA64EL0 = true) :
    ∃ p t, EventParts.prepareV s = .ok p t ∧ TimerFrame s t ∧ EventRange p :=
  ⟨eventVValue s, eventVState s, event_prepare_v_eq s ha, event_v_frame s, event_v_range s⟩

#print axioms event_prepare_v
end HookQuietCounters
