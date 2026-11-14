import HookQuietCounters.EventRun
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.CounterRun.counter_tail_total"
  (← IO.getStderr).flush

theorem counter_tail_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (prior : BitVec 64) :
    ∃ t, afterIncrement prior s = .ok () t ∧ TimerFrame s t ∧
      ArmCert.HookQuiet.V0.HookQuiet budget t := by
  obtain ⟨s1, ht, ft, q1⟩ := a64_timers_total budget s q
  obtain ⟨s2, hp, fp, q2⟩ := event_p_total budget s1 q1 prior (physicalValue s1)
  obtain ⟨s3, hv, fv, q3⟩ := event_v_total budget s2 q2 prior (physicalValue s2)
  refine ⟨s3, ?_, (ft.trans fp).trans fv, q3⟩
  simp only [afterIncrement, bind_app, have_a64 s q.a64, Bool.not_true,
    Bool.false_eq_true, reduceIte, ht, physical_count_apply, hp, hv]

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CounterRun.CounterPost"
  (← IO.getStderr).flush

structure CounterPost (budget : Nat) (s t : NativeState) : Prop where
  frame : E22Frame s.regs t.regs
  bits : ArmCert.HookQuiet.V0.TimerLowBitsEq s.regs t.regs
  gic : t.regs.bank_Option_InterruptID .__GIC_Pending = s.regs.bank_Option_InterruptID .__GIC_Pending
  mem : t.mem = s.mem
  events : t.events = s.events
  choiceState : t.choiceState = s.choiceState
  tags : t.tags = s.tags
  cycleCount : t.cycleCount = s.cycleCount
  sailOutput : t.sailOutput = s.sailOutput
  quiet : ArmCert.HookQuiet.V0.HookQuiet budget t

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CounterRun.CounterPost.of_timer"
  (← IO.getStderr).flush

theorem CounterPost.of_timer {budget : Nat} {s t : NativeState}
    (f : TimerFrame s t) (q : ArmCert.HookQuiet.V0.HookQuiet budget t) :
    CounterPost budget s t :=
  ⟨f.frame, f.bits, f.gic, f.mem, f.events, f.choiceState, f.tags, f.cycleCount, f.sailOutput, q⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CounterRun.counter_tick_total"
  (← IO.getStderr).flush

theorem counter_tick_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet (budget+1) s) :
    ∃ t, (GenericCounterTick () : SailM Unit) s = .ok () t ∧ CounterPost budget s t := by
  rw [counter_prefix_quiet budget s q]
  split
  · have q0 := ArmCert.HookQuiet.V0.hookQuiet_mono (Nat.le_succ budget) q
    obtain ⟨t, ht, ft, qt⟩ := a64_timers_total budget s q0
    exact ⟨t, ht, CounterPost.of_timer ft qt⟩
  · obtain ⟨t, ht, ft, qt⟩ := counter_tail_total budget (advanceCount s)
      (advance_quiet budget s q) (physicalValue s)
    refine ⟨t, ht, ?_⟩
    have hb : ArmCert.HookQuiet.V0.TimerLowBitsEq s.regs (advanceCount s).regs := by
      constructor <;> exact ⟨rfl, rfl⟩
    exact ⟨ft.frame.trans rfl, lowbits_trans hb ft.bits, ft.gic, ft.mem, ft.events,
      ft.choiceState, ft.tags, ft.cycleCount, ft.sailOutput, qt⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CounterRun.system_counter_total"
  (← IO.getStderr).flush

theorem system_counter_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet (budget+1) s) :
    ∃ t, (__UpdateSystemCounter () : SailM Unit) s = .ok () t ∧ CounterPost budget s t := by
  exact counter_tick_total budget s q
#print axioms counter_tail_total
#print axioms counter_tick_total
#print axioms system_counter_total
end HookQuietCounters
