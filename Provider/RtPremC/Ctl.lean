-- RtPremC.Ctl (, premise C): the translation-control register vector ctlv and its
-- preservation through each layer of one actual heap-v2 step (fetch, PMU E20 hook, metadata, action frame,
-- NonProj epilogue). Feeds ControlsRestored / E26CoveredUnchanged across the body.
import RtDit2.DitBodyM
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
namespace RtPremC

/-- Every register field ControlsRestored and E26CoveredUnchanged read. -/
def ctlv (r : Regs) :=
  (r.FeatureImpl, r.PSTATE.EL, r.PSTATE.nRW, r.bank_Bool .__tlb_enabled,
   (r.bank_BitVec_64 .TCR_EL2, r.bank_BitVec_64 .TCR2_EL2, r.bank_BitVec_64 .HCR_EL2, r.bank_BitVec_64 .SCR_EL3,
    r.bank_BitVec_64 .SCTLR_EL2, r.bank_BitVec_64 .MAIR_EL2, r.bank_BitVec_64 .HTTBR,
    r.bank_BitVec_64 .PIR_EL2, r.bank_BitVec_64 .PIRE0_EL2, r.bank_BitVec_64 .POR_EL0),
   (r.bank_BitVec_128 ._TTBR0_EL2, r.bank_BitVec_128 .TTBR1_EL2),
   (r.bank_Int .__supported_pa_size, r.bank_Int .__block_bbm_implemented))

theorem ctl_fetched (acc : AccessDescriptor) (nx : TTWState) (s : NativeState) :
    ctlv (FetchedRegs acc nx s) = ctlv s.regs :=
  ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field ctlv acc nx s (fun _ _ => rfl) (fun _ => rfl)
    (by simp (disch := decide) only [ctlv, ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne])

theorem ctl_e20 (fetched sp : NativeState) (budget : Nat) (quiet : HookQuiet (budget + 1) fetched)
    (hook : (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp) :
    ctlv sp.regs = ctlv fetched.regs :=
  frame_pres_E20 ctlv (fun x => by simp (disch := decide) only [ctlv, eraseE20, RegMap.set_ne])
    (entry_spec_post fetched sp (budget + 1) quiet hook).frame

theorem ctl_action (w : BitVec 32) (sp : NativeState) (K : Int) :
    ctlv (actionState w sp K).regs = ctlv sp.regs := by
  simp (disch := decide) only [ctlv, actionState, RegMap.set_ne]

theorem ctl_frame {writes : NativeEntry.Effects.Writes} {t u : NativeState}
    (h : NativeEntryContract.Frame writes t u) : ctlv u.regs = ctlv t.regs := by
  have el : u.regs.PSTATE.EL = t.regs.PSTATE.EL := by
    have e := congrArg ProcState.EL h.pse; unfold NativeEntryContract.erasePState at e; split at e <;> exact e
  have nrw : u.regs.PSTATE.nRW = t.regs.PSTATE.nRW := by
    have e := congrArg ProcState.nRW h.pse; unfold NativeEntryContract.erasePState at e; split at e <;> exact e
  simp only [ctlv, h.feat, h.bbool, h.b64, h.b128, h.bint, el, nrw]

theorem ctl_frameBr {t u : NativeState} (h : ArmBridge.CruxGenBr.ActFrameBr t u) : ctlv u.regs = ctlv t.regs := by
  have el : u.regs.PSTATE.EL = t.regs.PSTATE.EL := by have e := congrArg ProcState.EL h.pse; exact e
  have nrw : u.regs.PSTATE.nRW = t.regs.PSTATE.nRW := by have e := congrArg ProcState.nRW h.pse; exact e
  have tlb : u.regs.bank_Bool .__tlb_enabled = t.regs.bank_Bool .__tlb_enabled := h.bbool _ (by decide)
  simp only [ctlv, h.feat, h.b64, h.b128, h.bint, el, nrw, tlb]

theorem ctl_np {r r' : Regs} (np : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap r r') :
    ctlv r' = ctlv r := by
  have e := congrArg ctlv np
  simp only [ctlv, ArmCertCT.CT2.mask] at e
  simpa (config := {decide := true}) [ctlv, ArmCertCT.CT2.maskBank, ArmCertCT.CT2.maskPSTATE,
    ArmBridge.CruxNonProj.bkHeap] using e

#print axioms ctl_fetched
#print axioms ctl_e20
#print axioms ctl_action
#print axioms ctl_frame
#print axioms ctl_frameBr
#print axioms ctl_np
end RtPremC
