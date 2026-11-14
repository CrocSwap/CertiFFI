import Bridge.CruxGenGuarded.HookLaws
import HookQuietCounters.CounterRun
import HookQuietCounters.PMUEventNonRetired
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded.Owner
open ArmBridge.Draft ArmBridge.CruxCore
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/- Actual native-owner laws, projected into Core's internal pointwise
interface. Both cover the full Q-v0 domain. Retired-PMU and cycle-PMU remain
separate unconstructed obligations; no full HookLaws instance is supplied. -/

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.Owner.counter_rule"
  (← IO.getStderr).flush

theorem counter_rule (budget : Nat) (s : NativeState) (q : HookQuiet (budget + 1) s) :
    ∃ t, (__UpdateSystemCounter () : SailM Unit) s = .ok () t ∧ HookPost E22Frame budget s t := by
  obtain ⟨t, ht, post⟩ := HookQuietCounters.system_counter_total budget s q
  exact ⟨t, ht, post.frame, post.gic, post.mem, post.events, post.quiet⟩

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.Owner.spec_rule"
  (← IO.getStderr).flush

theorem spec_rule : EventLaw PMU_EVENT_INST_SPEC := by
  intro budget s q
  obtain ⟨t, ht, post⟩ := HookQuietCounters.pmu_spec_total budget s q
  exact ⟨t, ht, post.frame, post.gic, post.mem, post.events, post.quiet⟩

#print axioms counter_rule
#print axioms spec_rule
end ArmBridge.CruxGenGuarded.Owner
