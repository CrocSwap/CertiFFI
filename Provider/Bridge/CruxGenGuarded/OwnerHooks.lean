import Bridge.CruxGenGuarded.OwnerCounterSpec
import Bridge.CruxGenGuarded.OwnerRetired
import HookQuietCounters.PMUCycleRun
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

/- Constructed full-Q native hook bundle. Fixed native class factories apply
this constant internally; callers supply no hook law or future-state answer.
Consumer admission, fixed class proofs and joint satisfiability remain separate. -/

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.Owner.cycle_rule"
  (← IO.getStderr).flush

theorem cycle_rule (budget : Nat) (s : NativeState) (q : HookQuiet budget s) :
    ∃ t, (AArch64_PMUCycle () : SailM Unit) s = .ok () t ∧ HookPost E20Frame budget s t := by
  obtain ⟨t, ht, post⟩ := HookQuietCounters.pmu_cycle_total budget s q
  exact ⟨t, ht, post.frame, post.gic, post.mem, post.events, post.quiet⟩

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.Owner.hook_laws"
  (← IO.getStderr).flush

theorem hook_laws : HookLaws :=
  ⟨spec_rule, retired_rule, counter_rule, cycle_rule⟩

#print axioms cycle_rule
#print axioms hook_laws
end ArmBridge.CruxGenGuarded.Owner
