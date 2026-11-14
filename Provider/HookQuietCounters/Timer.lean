import HookQuietCounters.PMUOff
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.Timer.physicalValue"
  (← IO.getStderr).flush

def physicalValue (s : NativeState) : BitVec 64 :=
  Sail.BitVec.extractLsb s.regs.PhysicalCount 87 24

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Timer.timerStatus"
  (← IO.getStderr).flush

def timerStatus (s : NativeState) (offset deadline : BitVec 64) : Bool :=
  (((BitVec.toNat (physicalValue s - offset)) -i (BitVec.toNat deadline)) ≥b 0)

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Timer.physical_count_apply"
  (← IO.getStderr).flush

theorem physical_count_apply (s : NativeState) :
    (PhysicalCountInt () : SailM (BitVec 64)) s = .ok (physicalValue s) s := rfl

/- The model does not clear an existing pending interrupt on a low signal. -/
run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Timer.irq_low"
  (← IO.getStderr).flush

theorem irq_low (irq : InterruptID) (s : NativeState) :
    (SetInterruptRequestLevel irq Signal.Signal_Low : SailM Unit) s = .ok () s := by
  have h : (Signal.Signal_Low == Signal.Signal_High) = false := by decide
  simp only [SetInterruptRequestLevel, bind_app, pure_apply, map_apply, h,
    Bool.false_eq_true, ↓reduceIte]

/- Masking suppresses the interrupt write, but does not force ISTATUS false. -/
run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Timer.timer_masked"
  (← IO.getStderr).flush

theorem timer_masked (offset deadline : BitVec 64) (irq : InterruptID) (s : NativeState) :
    (IsTimerConditionMet offset deadline 1#1 irq : SailM Bool) s =
      .ok (timerStatus s offset deadline) s := by
  simp [IsTimerConditionMet, bind_app, pure_apply, map_apply,
    physical_count_apply, timerStatus, irq_low]

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Timer.timer_status_future"
  (← IO.getStderr).flush

theorem timer_status_future (offset deadline : BitVec 64) (s : NativeState)
    (h : (physicalValue s - offset).toNat < deadline.toNat) :
    timerStatus s offset deadline = false := by
  change decide (((physicalValue s - offset).toNat : Int) - (deadline.toNat : Int) ≥ 0) = false
  simp only [decide_eq_false_iff_not]
  omega

/- The input is a concrete unsigned comparison after the model's modular subtraction.
No-wrap propagation for a future horizon is a separate arithmetic obligation. -/
run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Timer.timer_future"
  (← IO.getStderr).flush

theorem timer_future (offset deadline : BitVec 64) (mask : BitVec 1)
    (irq : InterruptID) (s : NativeState)
    (h : (physicalValue s - offset).toNat < deadline.toNat) :
    (IsTimerConditionMet offset deadline mask irq : SailM Bool) s = .ok false s := by
  have hs := timer_status_future offset deadline s h
  simp only [timerStatus] at hs
  simp only [IsTimerConditionMet, bind_app, pure_apply, map_apply, physical_count_apply]
  simp only [hs, Bool.false_and, Bool.false_eq_true, ↓reduceIte, irq_low, pure_apply]

#print axioms irq_low
#print axioms timer_masked
#print axioms timer_status_future
#print axioms timer_future

end HookQuietCounters
