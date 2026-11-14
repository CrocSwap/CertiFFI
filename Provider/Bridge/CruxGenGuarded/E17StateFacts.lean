import Bridge.CruxGenGuarded.EntryBtiNext
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
namespace ArmBridge.CruxGenGuarded.E17StateFacts
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! E17 run join, Core side of the per-reached-state invariant:
every chained reached state carries CurrentS1At (here recovered at the state
itself from its `beforeFetchState`), HostEL0ModeAt, F4, the existing E11
MDE/HDE projection and SPESampleInFlight=false. ClosedMembershipAt is the
remaining per-state input. -/

theorem current_of_before_fetch {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} (x : NativeState)
    (h : CurrentS1At spec config rows (ArmBridge.CruxGenGuarded.beforeFetchState x)) :
    CurrentS1At spec config rows x := by
  refine current_s1_program_write h (fun _ => False)
    (EntryBtiNext.no_writes _ x rfl) (EntryBtiNext.no_writes_separated _) rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ rfl
    (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) rfl
  all_goals simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne]

run_cmd do
  IO.eprintln "CURRENT_DECL E17StateFacts.state_facts"
  (← IO.getStderr).flush

theorem state_facts {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} (x : NativeState)
    (pins : NativeEntryTail.EntryPins x) (features : EntryFeatures x.regs)
    (e11 : E11Debug.E11CheckDebug x.regs)
    (current : CurrentS1At spec config rows (ArmBridge.CruxGenGuarded.beforeFetchState x)) :
    CurrentS1At spec config rows x ∧ HostEL0ModeAt x.regs ∧ x.regs.FeatureImpl[4] = true ∧
      ExistingE11DebugAt x.regs ∧ x.regs.bank_Bool .SPESampleInFlight = false :=
  ⟨current_of_before_fetch x current,
   ⟨features.a2, features.b2, features.vhe, pins.el, pins.scrns, pins.tge⟩,
   by simpa using pins.f4, ⟨e11.mde, e11.hde⟩, pins.spe⟩

#print axioms current_of_before_fetch
#print axioms state_facts
end ArmBridge.CruxGenGuarded.E17StateFacts
