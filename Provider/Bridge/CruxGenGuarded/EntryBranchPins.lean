import Bridge.CruxGenGuarded.EntryControls
import Bridge.CruxGenGuarded.EntryEpilogue
import SDKPA.BrPinsStep
import NativeEntryInput.Input
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace ArmBridge.CruxGenGuarded.EntryBranchPins
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! Branch classes (cad54ca) need `Crypto.BranchPinsV2` at the ACTION
state. It is a fixed platform profile carried at the fetched state (like
StepPins) and moved fetched → E20 (spec PMU) → actionState by crypto's
`branchPinsV2_step`, from SysEq2 (Input), StepPins at the action state and
BrSysEq (E20 erases only PMU counters; metadata writes SEE only). -/

theorem sysEq2_symm (r r' : Regs) (h : SysEq2 r r') : SysEq2 r' r :=
  ⟨h.feat.symm, h.el.symm, h.nrw.symm, h.sctlr.symm, h.tcr.symm, h.tcr2.symm, h.hcr.symm,
   h.scr.symm, h.mair.symm, h.mdscr.symm, h.httbr.symm, h.ttbr0.symm, h.ttbr1.symm, h.hde.symm,
   h.tlb.symm, h.spe.symm, h.pa.symm⟩

theorem brSysEq_trans (a b c : Regs) (hab : BrSysEq a b) (hbc : BrSysEq b c) : BrSysEq a c :=
  ⟨hbc.nbp.trans hab.nbp, hbc.nwp.trans hab.nwp, hbc.nctx.trans hab.nctx, hbc.mdcr3.trans hab.mdcr3⟩

theorem brSysEq_e20 (r r' : Regs) (h : E20Frame r r') : BrSysEq r r' := by
  refine ⟨frame_pres_E20 (fun x => x.bank_Int .NUM_BREAKPOINTS) ?_ h,
    frame_pres_E20 (fun x => x.bank_Int .NUM_WATCHPOINTS) ?_ h,
    frame_pres_E20 (fun x => x.bank_Int .__num_ctx_breakpoints) ?_ h,
    frame_pres_E20 (fun x => x.bank_BitVec_64 .MDCR_EL3) ?_ h⟩ <;>
  intro x <;> simp (disch := decide) only [eraseE20, RegMap.set_ne]

theorem brSysEq_action (w : BitVec 32) (sp : NativeState) (K : Int) :
    BrSysEq sp.regs (actionState w sp K).regs := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp (disch := decide) only [actionState, RegMap.set_ne] <;> split <;> rfl

run_cmd do
  IO.eprintln "CURRENT_DECL EntryBranchPins.branch_pins_action"
  (← IO.getStderr).flush

/-- BranchPinsV2 at the action state of a fixed class word. -/
theorem branch_pins_action (source fetched sp : NativeState) (w : BitVec 32) (K : Int)
    (input : NativeEntryInput.Input source fetched)
    (metadata : NativeEntryInput.Input source (actionState w sp K))
    (e20 : E20Frame fetched.regs sp.regs)
    (pinsT : StepPins (actionState w sp K))
    (bp : Crypto.BranchV2.BranchPinsV2PA fetched) :
    Crypto.BranchV2.BranchPinsV2PA (actionState w sp K) :=
  Crypto4.branchPinsV2_step_pa fetched (actionState w sp K) bp
    (sysEq2_trans _ _ _ input.sys (sysEq2_symm _ _ metadata.sys)) pinsT
    (brSysEq_trans _ _ _ (brSysEq_e20 _ _ e20) (brSysEq_action w sp K))

#print axioms branch_pins_action
end ArmBridge.CruxGenGuarded.EntryBranchPins
