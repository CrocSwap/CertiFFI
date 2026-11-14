import HookQuietCounters.IncrementEventTail
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.IncrementEventRun.increment_event_counter_total"
  (← IO.getStderr).flush

theorem increment_event_counter_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat) (inc : Int) (hn : idx < 31) :
    ∃ t, (AArch64_IncrementEventCounter idx inc : SailM Unit) s = .ok () t ∧ PMUPost budget s t := by
  obtain ⟨⟨oldValue, newValue⟩, a, ha, fa⟩ := increment_event_prefix budget s q idx inc hn
  obtain ⟨lp, width, w, hw, fw, _⟩ := increment_event_middle budget a fa.quiet idx newValue
  obtain ⟨t, ht, ft⟩ := increment_event_tail budget w fw.quiet idx oldValue newValue lp width
  refine ⟨t, ?_, (fa.trans fw).trans ft⟩
  rw [IncrementEventParts.equation]
  simp only [bind_app, ha, hw, ht]
#print axioms increment_event_counter_total
end HookQuietCounters
