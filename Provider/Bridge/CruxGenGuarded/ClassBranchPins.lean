import Bridge.CruxGenGuarded.EntryClassNext
import Bridge.CruxGenGuarded.EntryBranchPins
import Bridge.CruxGenGuarded.BookkeepingTransport
import Bridge.CruxGenGuarded.FrameTransport
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace ArmBridge.CruxGenGuarded.ClassBranchPins
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! BranchPinsV2 across a NON-branch fixed-class step, from exactly what
`ClassTail`/`ClassTailAt` already export (spec PMU hook, Contract.Frame at the
action state, SysEq2 + bkHeap NPE action→fin, StepPins fin): no adapter change. -/

theorem erase_el (writes : NativeEntry.Effects.Writes) (p : ProcState) :
    (NativeEntryContract.erasePState writes p).EL = p.EL := by
  unfold NativeEntryContract.erasePState; split <;> rfl

theorem erase_nrw (writes : NativeEntry.Effects.Writes) (p : ProcState) :
    (NativeEntryContract.erasePState writes p).nRW = p.nRW := by
  unfold NativeEntryContract.erasePState; split <;> rfl

theorem frame_sys (writes : NativeEntry.Effects.Writes) (t u : NativeState)
    (h : NativeEntryContract.Frame writes t u) : SysEq2 t.regs u.regs := by
  have el : u.regs.PSTATE.EL = t.regs.PSTATE.EL := by
    have := congrArg ProcState.EL h.pse
    rwa [erase_el, erase_el] at this
  have nrw : u.regs.PSTATE.nRW = t.regs.PSTATE.nRW := by
    have := congrArg ProcState.nRW h.pse
    rwa [erase_nrw, erase_nrw] at this
  exact ⟨h.feat, el, nrw, congrFun h.b64 _, congrFun h.b64 _, congrFun h.b64 _, congrFun h.b64 _,
    congrFun h.b64 _, congrFun h.b64 _, congrFun h.b64 _, congrFun h.b64 _, congrFun h.b128 _,
    congrFun h.b128 _, by rw [h.b32], congrFun h.bbool _, congrFun h.bbool _, congrFun h.bint _⟩

theorem frame_branch (writes : NativeEntry.Effects.Writes) (t u : NativeState)
    (h : NativeEntryContract.Frame writes t u) : BrSysEq t.regs u.regs :=
  ⟨congrFun h.bint _, congrFun h.bint _, congrFun h.bint _, congrFun h.b64 _⟩

theorem npe_branch (r r' : Regs) (h : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap r r') :
    BrSysEq r r' := by
  unfold ArmCertCT.CT2.NonProjRegsEq at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := congrArg (fun x : Regs => x.bank_Int .NUM_BREAKPOINTS) h
    simpa [ArmCertCT.CT2.mask, ArmCertCT.CT2.maskBank, ArmBridge.CruxNonProj.bkHeap] using this
  · have := congrArg (fun x : Regs => x.bank_Int .NUM_WATCHPOINTS) h
    simpa [ArmCertCT.CT2.mask, ArmCertCT.CT2.maskBank, ArmBridge.CruxNonProj.bkHeap] using this
  · have := congrArg (fun x : Regs => x.bank_Int .__num_ctx_breakpoints) h
    simpa [ArmCertCT.CT2.mask, ArmCertCT.CT2.maskBank, ArmBridge.CruxNonProj.bkHeap] using this
  · have := congrArg (fun x : Regs => x.bank_BitVec_64 .MDCR_EL3) h
    simpa [ArmCertCT.CT2.mask, ArmCertCT.CT2.maskBank, ArmBridge.CruxNonProj.bkHeap] using this

run_cmd do
  IO.eprintln "CURRENT_DECL ClassBranchPins.class_branch_pins"
  (← IO.getStderr).flush

theorem class_branch_pins (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (fetched sp a fin : NativeState) (budget : Nat)
    (pins : StepPins fetched) (quiet : HookQuiet (budget + 1) fetched)
    (hook : (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp)
    (frame : NativeEntryContract.Frame writes (actionState w sp K) a)
    (sys : SysEq2 a.regs fin.regs)
    (np : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs)
    (pinsFin : StepPins fin)
    (bp : Crypto.BranchV2.BranchPinsV2PA fetched) : Crypto.BranchV2.BranchPinsV2PA fin := by
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have entrySp := NativeEntryTail.EntryPins.after_E20 fetched sp
    (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame
  have btype : sp.regs.PSTATE.BTYPE = 0#2 := by
    rw [(PMUFrame.of_E20 post.frame).pstate]; exact pins.btype
  have btn : sp.regs.BTypeNext = 0#2 := (PMUFrame.of_E20 post.frame).btn.trans pins.btn
  have spPins : StepPins sp := scalar_pins sp entrySp btype btn
  have s1 := sysEq2_trans _ _ _ (e20_sys _ _ post.frame) (metadata_sys w sp K spPins)
  have s2 := sysEq2_trans _ _ _ (sysEq2_trans _ _ _ s1 (frame_sys writes _ a frame)) sys
  have b1 := EntryBranchPins.brSysEq_trans _ _ _ (EntryBranchPins.brSysEq_e20 _ _ post.frame)
    (EntryBranchPins.brSysEq_action w sp K)
  have b2 := EntryBranchPins.brSysEq_trans _ _ _
    (EntryBranchPins.brSysEq_trans _ _ _ b1 (frame_branch writes _ a frame)) (npe_branch _ _ np)
  exact Crypto4.branchPinsV2_step_pa fetched fin bp s2 pinsFin b2

#print axioms class_branch_pins
end ArmBridge.CruxGenGuarded.ClassBranchPins
