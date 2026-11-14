import Bridge.CruxGenGuarded.EntryClassNext
import Bridge.CruxGenGuarded.EntryBranchPins
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
namespace ArmBridge.CruxGenGuarded.EntryFetchedBranch
open ArmCertWalk ArmBridge.Boundary
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen
open ArmBridge.CruxGenGuarded.EntryFetchedFacts ArmBridge.CruxGenGuarded.EntryClassNext
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! BranchPinsV2 across the ACTUAL fetch: from the step-start state to the actual
fetched state (`FetchedRegs`), so the chain can hand it to branch class tails. -/

theorem fetched_brSysEq (acc : AccessDescriptor) (next : TTWState) (s t : NativeState)
    (hregs : t.regs = FetchedRegs acc next s) : BrSysEq s.regs t.regs := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  (rw [hregs]; unfold FetchedRegs fetchGuardRegs; split <;> rfl)

run_cmd do
  IO.eprintln "CURRENT_DECL EntryFetchedBranch.fetched_branch_pins"
  (← IO.getStderr).flush

theorem fetched_branch_pins (acc : AccessDescriptor) (next : TTWState) (s t : NativeState)
    (hp : StepPins s) (hregs : t.regs = FetchedRegs acc next s)
    (bp : Crypto.BranchV2.BranchPinsV2PA s) : Crypto.BranchV2.BranchPinsV2PA t :=
  Crypto4.branchPinsV2_step_pa s t bp
    (EntryBranchPins.sysEq2_symm _ _ (fetched_input acc next s t hp.el hregs).sys)
    (fetched_steppins acc next s t hp hregs) (fetched_brSysEq acc next s t hregs)

#print axioms fetched_branch_pins
end ArmBridge.CruxGenGuarded.EntryFetchedBranch
