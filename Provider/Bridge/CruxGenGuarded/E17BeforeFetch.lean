-- Generic lemma split out of Bridge.CruxGenGuarded.E17NonVacuity ((3)); name and proof unchanged.
import Bridge.CruxGenGuarded.E17StateFacts
import Bridge.CruxGenGuarded.ChainInv
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
namespace ArmBridge.CruxGenGuarded.E17NonVacuity
open ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded.EntryActualFetch
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000


/-- `beforeFetchState` only touches registers the canonical invariant does not
read (converse of `E17StateFacts.current_of_before_fetch`). -/
theorem before_fetch_of_current {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} (x : NativeState)
    (h : CurrentS1At spec config rows x) :
    CurrentS1At spec config rows (ArmBridge.CruxGenGuarded.beforeFetchState x) := by
  refine current_s1_program_write h (fun _ => False)
    (EntryBtiNext.no_writes x _ rfl) (EntryBtiNext.no_writes_separated _) rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ rfl
    (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) rfl
  all_goals simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne]

#print axioms before_fetch_of_current
end ArmBridge.CruxGenGuarded.E17NonVacuity
