import HookQuietCounters.EventPrepare
import HookQuietCounters.EventEdges
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventRun.event_p_total"
  (← IO.getStderr).flush

theorem event_p_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (prev current : BitVec 64) :
    ∃ t, (TestEventCNTP prev current : SailM Unit) s = .ok () t ∧
      TimerFrame s t ∧ ArmCert.HookQuiet.V0.HookQuiet budget t := by
  obtain ⟨p, s1, hp, fp, hr⟩ := event_prepare_p s q.a64
  rw [EventParts.equationP]
  cases p with
  | none =>
    exact ⟨s1, by simp only [bind_app, hp, pure_apply], fp, fp.quiet q⟩
  | some p =>
    obtain ⟨t, he, fe⟩ := EventEdges.totalP s1 prev current p.1 p.2 hr
    exact ⟨t, by simp only [bind_app, hp, he], fp.trans fe, (fp.trans fe).quiet q⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.EventRun.event_v_total"
  (← IO.getStderr).flush

theorem event_v_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (prev current : BitVec 64) :
    ∃ t, (TestEventCNTV prev current : SailM Unit) s = .ok () t ∧
      TimerFrame s t ∧ ArmCert.HookQuiet.V0.HookQuiet budget t := by
  obtain ⟨p, s1, hp, fp, hr⟩ := event_prepare_v s q.a64
  rw [EventParts.equationV]
  cases p with
  | none =>
    exact ⟨s1, by simp only [bind_app, hp, pure_apply], fp, fp.quiet q⟩
  | some p =>
    obtain ⟨t, he, fe⟩ := EventEdges.totalV s1 prev current p.1 p.2 hr
    exact ⟨t, by simp only [bind_app, hp, he], fp.trans fe, (fp.trans fe).quiet q⟩
#print axioms event_p_total
#print axioms event_v_total
end HookQuietCounters
