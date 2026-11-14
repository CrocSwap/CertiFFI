import Bridge.CruxGenGuarded.HookLaws
import HookQuietCounters.PMUEventRun
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded.Owner
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/- Actual native-owner event laws, including retired events on the full Q-v0
domain. These project actual successful successors; no full HookLaws instance
is supplied until the separate cycle law has been constructed. -/

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.Owner.event_rule"
  (← IO.getStderr).flush

theorem event_rule (event : BitVec 16) : EventLaw event := by
  intro budget s q
  obtain ⟨t, ht, post⟩ := HookQuietCounters.pmu_event_total budget s q event
  exact ⟨t, ht, post.frame, post.gic, post.mem, post.events, post.quiet⟩

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.Owner.retired_rule"
  (← IO.getStderr).flush

theorem retired_rule : EventLaw PMU_EVENT_INST_RETIRED :=
  event_rule PMU_EVENT_INST_RETIRED

#print axioms event_rule
#print axioms retired_rule
end ArmBridge.CruxGenGuarded.Owner
