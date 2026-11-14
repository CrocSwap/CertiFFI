import HookQuietCounters.TimerRun
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

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventCore.uint"
  (← IO.getStderr).flush

theorem uint (label : ChoiceLabel) (s : NativeState) :
    ∃ n, (undefined_int_at label () : SailM Int) s = .ok n s := ⟨_, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventCore.eventState"
  (← IO.getStderr).flush

def eventState (s : NativeState) : NativeState :=
  let r : Regs := {s.regs with bank_BitVec_1 := RegMap.set s.regs.bank_BitVec_1 .EventRegister 1#1}
  {s with regs := r}

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventCore.set_event_apply"
  (← IO.getStderr).flush

theorem set_event_apply (s : NativeState) :
    (SetEventRegister () : SailM Unit) s = .ok () (eventState s) := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventCore.event_frame"
  (← IO.getStderr).flush

theorem event_frame (s : NativeState) : TimerFrame s (eventState s) := by
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [E22Frame, eraseE22, eventState, RegMap.set_set_same]
  · constructor <;> exact ⟨rfl, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventCore.event_index_range"
  (← IO.getStderr).flush

theorem event_index_range (i : BitVec 4) (high : Bool) :
    ((0 ≤b ((i.toNat : Int) + (if high then 8 else 0))) &&
      (((i.toNat : Int) + (if high then 8 else 0)) <b 64)) = true := by
  have hi := i.isLt
  cases high <;> simp <;> omega

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventCore.unit_bind"
  (← IO.getStderr).flush

theorem unit_bind (x : SailM Unit) : (x >>= fun _ => (pure () : SailM Unit)) = x := by
  have h : (fun _ : Unit => (pure () : SailM Unit)) = (pure : Unit → SailM Unit) := by
    funext u; cases u; rfl
  rw [h, bind_pure]

#print axioms unit_bind
#print axioms set_event_apply
#print axioms event_frame
#print axioms event_index_range

end HookQuietCounters
