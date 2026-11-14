import HookQuietCounters.TimerPrepare
import ArmCert.HookQuiet.V0.TransportE22Same
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerCompose.lowbits_trans"
  (← IO.getStderr).flush

theorem lowbits_trans {a b c : Regs}
    (hab : ArmCert.HookQuiet.V0.TimerLowBitsEq a b)
    (hbc : ArmCert.HookQuiet.V0.TimerLowBitsEq b c) :
    ArmCert.HookQuiet.V0.TimerLowBitsEq a c := by
  exact ⟨⟨hbc.p.1.trans hab.p.1, hbc.p.2.trans hab.p.2⟩,
    ⟨hbc.hp.1.trans hab.hp.1, hbc.hp.2.trans hab.hp.2⟩,
    ⟨hbc.hps.1.trans hab.hps.1, hbc.hps.2.trans hab.hps.2⟩,
    ⟨hbc.ps.1.trans hab.ps.1, hbc.ps.2.trans hab.ps.2⟩,
    ⟨hbc.v.1.trans hab.v.1, hbc.v.2.trans hab.v.2⟩,
    ⟨hbc.hv.1.trans hab.hv.1, hbc.hv.2.trans hab.hv.2⟩,
    ⟨hbc.hvs.1.trans hab.hvs.1, hbc.hvs.2.trans hab.hvs.2⟩⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerCompose.TimerFrame.trans"
  (← IO.getStderr).flush

theorem TimerFrame.trans {s t u : NativeState} (a : TimerFrame s t) (b : TimerFrame t u) :
    TimerFrame s u :=
  ⟨b.frame.trans a.frame, lowbits_trans a.bits b.bits, b.count.trans a.count,
    b.gic.trans a.gic, b.mem.trans a.mem, b.events.trans a.events,
    b.choiceState.trans a.choiceState, b.tags.trans a.tags,
    b.cycleCount.trans a.cycleCount, b.sailOutput.trans a.sailOutput⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerCompose.TimerFrame.quiet"
  (← IO.getStderr).flush

theorem TimerFrame.quiet {budget : Nat} {s t : NativeState}
    (f : TimerFrame s t) (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ArmCert.HookQuiet.V0.HookQuiet budget t :=
  ArmCert.HookQuiet.V0.hookQuiet_same_budget_E22_of_physicalCount_eq q f.frame f.bits f.count

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerCompose.TimerFrame.security_eq"
  (← IO.getStderr).flush

theorem TimerFrame.security_eq {s t : NativeState} (f : TimerFrame s t) :
    securityValue t = securityValue s := by
  exact frame_pres_E22 (fun r => securityValue {s with regs := r}) (fun _ => rfl) f.frame

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerCompose.TimerFrame.offset_eq"
  (← IO.getStderr).flush

theorem TimerFrame.offset_eq {s t : NativeState} (f : TimerFrame s t) :
    ArmCert.HookQuiet.V0.physicalOffset t.regs = ArmCert.HookQuiet.V0.physicalOffset s.regs :=
  frame_pres_E22 ArmCert.HookQuiet.V0.physicalOffset (fun _ => rfl) f.frame

/- Only occurrence bookkeeping is erased for this equality. The actual
successor is still passed to every subsequent model call. -/
run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerCompose.eraseOcc"
  (← IO.getStderr).flush

def eraseOcc (s : NativeState) : NativeState := {s with choiceOcc := {}}

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerCompose.erase_security_query"
  (← IO.getStderr).flush

theorem erase_security_query (s : NativeState) :
    eraseOcc (securityQueryState s) = eraseOcc s := by
  unfold securityQueryState
  split <;> rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerCompose.erase_el2_query"
  (← IO.getStderr).flush

theorem erase_el2_query (s : NativeState) :
    eraseOcc (el2QueryState s) = eraseOcc s := by
  unfold el2QueryState secureEL2QueryState
  split <;> first | rfl | (split <;> rfl)

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerCompose.erase_timer_prepare"
  (← IO.getStderr).flush

theorem erase_timer_prepare (s : NativeState) :
    eraseOcc (timerPrepareState s) = eraseOcc s := by
  unfold timerPrepareState
  split
  · exact (erase_el2_query _).trans (erase_security_query s)
  · exact erase_security_query s

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerCompose.TimerFrame.of_eraseOcc_eq"
  (← IO.getStderr).flush

theorem TimerFrame.of_eraseOcc_eq {s t : NativeState}
    (h : eraseOcc t = eraseOcc s) : TimerFrame s t := by
  have hr : t.regs = s.regs := by
    simpa only [eraseOcc] using congrArg (fun x : NativeState => x.regs) h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show E22Frame s.regs t.regs = (eraseE22 t.regs = eraseE22 s.regs) from rfl, hr]
  · rw [hr]; constructor <;> exact ⟨rfl, rfl⟩
  · exact congrArg Regs.PhysicalCount hr
  · exact congrArg (fun r : Regs => r.bank_Option_InterruptID .__GIC_Pending) hr
  · simpa only [eraseOcc] using congrArg (fun x : NativeState => x.mem) h
  · simpa only [eraseOcc] using congrArg (fun x : NativeState => x.events) h
  · simpa only [eraseOcc] using congrArg (fun x : NativeState => x.choiceState) h
  · simpa only [eraseOcc] using congrArg (fun x : NativeState => x.tags) h
  · simpa only [eraseOcc] using congrArg (fun x : NativeState => x.cycleCount) h
  · simpa only [eraseOcc] using congrArg (fun x : NativeState => x.sailOutput) h

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerCompose.timer_prepare_frame"
  (← IO.getStderr).flush

theorem timer_prepare_frame (s : NativeState) : TimerFrame s (timerPrepareState s) :=
  TimerFrame.of_eraseOcc_eq (erase_timer_prepare s)

#print axioms TimerFrame.trans
#print axioms TimerFrame.quiet
#print axioms TimerFrame.security_eq
#print axioms timer_prepare_frame

end HookQuietCounters
