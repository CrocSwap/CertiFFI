import DefaultHeapShimClass
import TranslateSpan.DefaultScalarTrace
import TranslateSpan.FPControlFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxCore ArmBridge.CruxGen
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.EntryClassNext
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV3
open ArmCert.HookQuiet.V0 (HookQuiet)
open HeapV2StepCerts NativeMteTagCheck TranslateSpan ReleaseProfile
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 4096
namespace DitShim243.ShimABI

structure Fields (source fin : NativeState) : Prop where
  fpcr : fin.regs.FPCR = source.regs.FPCR
  fpsr : fin.regs.FPSR = source.regs.FPSR
  z : fin.regs._Z = source.regs._Z
  tls : ArmCertMemPipe.TLSFrame.tp fin = ArmCertMemPipe.TLSFrame.tp source

theorem fields_of_frames (real : Type) [Sail.SailReal real]
    (word : BitVec 32) (K : Int) (source fetched sp action fin : NativeState)
    (budget : Nat) (input : NativeEntryInput.Input source fetched)
    (quiet : HookQuiet (budget + 1) fetched)
    (hook : (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp)
    {writes : NativeEntry.Effects.Writes}
    (frame : NativeEntryContract.Frame writes (actionState word sp K) action)
    (fpcr : writes.fpcr = false) (fpsr : writes.fpsr = false) (vector : writes.vector = false)
    (np : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap action.regs fin.regs) :
    Fields source fin := by
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have actionFPCR : action.regs.FPCR = sp.regs.FPCR := by
    have equal := congrArg (fun r : Regs => r.FPCR) frame.nonProj
    simpa [NativeEntry.Effects.mask,NativeEntry.Effects.erase,ArmCertCT.CT2.mask,actionState,fpcr] using equal
  have actionFPSR : action.regs.FPSR = sp.regs.FPSR := by
    have equal := congrArg (fun r : Regs => r.FPSR) frame.nonProj
    simpa [NativeEntry.Effects.mask,NativeEntry.Effects.erase,ArmCertCT.CT2.mask,actionState,fpsr] using equal
  have actionZ : action.regs._Z = sp.regs._Z := by
    have equal := congrArg (fun r : Regs => r._Z) frame.nonProj
    simpa [NativeEntry.Effects.mask,NativeEntry.Effects.erase,ArmCertCT.CT2.mask,actionState,vector] using equal
  have actionTLS : ArmCertMemPipe.TLSFrame.tp action = ArmCertMemPipe.TLSFrame.tp sp := by
    unfold ArmCertMemPipe.TLSFrame.tp
    rw [frame.b64]; rfl
  have pmuFPCR : sp.regs.FPCR = fetched.regs.FPCR := frame_pres_E20 (fun r => r.FPCR) (fun _ => rfl) post.frame
  have pmuFPSR : sp.regs.FPSR = fetched.regs.FPSR := frame_pres_E20 (fun r => r.FPSR) (fun _ => rfl) post.frame
  have pmuZ : sp.regs._Z = fetched.regs._Z := frame_pres_E20 (fun r => r._Z)
    (fun r => by simp (disch := decide) only [eraseE20,RegMap.set_ne]) post.frame
  have pmuTLS : ArmCertMemPipe.TLSFrame.tp sp = ArmCertMemPipe.TLSFrame.tp fetched := by
    unfold ArmCertMemPipe.TLSFrame.tp
    exact frame_pres_E20 (fun r => r.bank_BitVec_64 .TPIDR_EL0)
      (fun r => by simp (disch := decide) only [eraseE20,RegMap.set_ne]) post.frame
  have finalZ : fin.regs._Z = action.regs._Z := by
    have equal := congrArg (fun r : Regs => r._Z) np
    simpa [ArmCertCT.CT2.mask] using equal
  exact ⟨(ArmBridge.CruxNonProj.fFPCR np).trans (actionFPCR.trans
      (pmuFPCR.trans (ArmBridge.CruxNonProj.fFPCR input.controls.nonProj))),
    (ArmBridge.CruxNonProj.fFPSR np).trans (actionFPSR.trans
      (pmuFPSR.trans (ArmBridge.CruxNonProj.fFPSR input.controls.nonProj))),
    finalZ.trans (actionZ.trans (pmuZ.trans input.z.symm)),
    (ArmCertMemPipe.TLSFrame.nonProj np).trans (actionTLS.trans
      (pmuTLS.trans (ArmCertMemPipe.TLSFrame.nonProj input.controls.nonProj)))⟩

theorem native_class (real : Type) [Sail.SailReal real]
    (word : BitVec 32) (K : Int) (source fetched fin : NativeState) (enc : __InstrEnc) (budget : Nat)
    (next : BitVec 64) (updates : List (RegBind.Reg × RegBind.Upd))
    (writes : NativeEntry.Effects.Writes)
    (tail : RegVal.ClassTailVAt real word writes K source next updates)
    (noFPCR : writes.fpcr = false) (noFPSR : writes.fpsr = false) (noVector : writes.vector = false)
    (pins : StepPins fetched) (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (quiet : HookQuiet (budget + 1) fetched)
    (it : fetched.regs.ShouldAdvanceIT = false) (ss : fetched.regs.ShouldAdvanceSS = true)
    (actual : nativeTail real source word enc fetched = .ok () fin) : Fields source fin := by
  obtain ⟨sp,action,returned,hook,run,frame,_,_,_,_,_,_,np,_⟩ :=
    tail fetched enc budget pins input guard quiet it ss
  have same : returned = fin := congrArg (resSt source) (run.symm.trans actual)
  subst returned
  exact fields_of_frames real word K source fetched sp action fin budget input quiet hook frame noFPCR noFPSR noVector np

theorem fetched_of_step (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (catalogue : ControlCatalogue) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0)
    (aligned : (offset k).toNat % 4 = 0) (word : BitVec 32) (source fin : NativeState)
    (core : DefaultCurrent.CurrentInv spec config rows mapping consumer scope image loadBase
      base offset budget k catalogue source)
    (ob : FetchObligations spec config rows mapping word source)
    (stepRun : modelStep real source = .ok () fin) :
    ∃ (fetched : NativeState) (enc : __InstrEnc),
      StepPins fetched ∧ NativeEntryInput.Input source fetched ∧ MetadataGuard fetched ∧
      HookQuiet ((budget - (k + 1)) + 1) fetched ∧
      fetched.regs.ShouldAdvanceIT = false ∧ fetched.regs.ShouldAdvanceSS = true ∧
      nativeTail real source word enc fetched = .ok () fin ∧ ChoiceDelta source fetched 0 ∧
      ∃ (acc : AccessDescriptor) (nx : TTWState), fetched.regs = FetchedRegs acc nx source := by
  have pins := NativeEntryTail.EntryPins.of_scalar source core.v1.pins
  obtain ⟨step, el, il, _pc, emu0, e11, mode, spe⟩ :=
    before_fetch_facts source pins core.v1.features core.v1.debug
  obtain ⟨acc, word', fetched, address, faultOut, translated, data, actualAcc, run, clean,
      bytes, fregs, _fmem, _fev, _current, _, fetchChoice,
      _info, _walk, _leaf, _middle, _len, _traffic, _tev, _noUpd⟩ :=
    native_fetch_current_preserving_events_choice spec config rows mapping (beforeFetchState source)
      step el (pc_low_of_placement _ base (offset k) core.v1.pc page aligned) il
      core.v1.current mode step.b0 ⟨e11.mde,e11.hde⟩ spe
      ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc
  have wordEqual := ob.code acc data.leafLevel data.view faultOut address translated word' clean bytes
  subst wordEqual
  obtain ⟨_, out, _, _, _, _, _, _, _, _, _, _, _, translatedRegs, _⟩ := clean
  have regs : fetched.regs = FetchedRegs acc (translateCurrent out) source := by
    rw [fregs,translatedRegs,ob.rawOf acc]
    rfl
  have emuFinal : fetched.regs.__emulator_termination_opcode = none := by
    rw [regs]
    unfold FetchedRegs fetchGuardRegs
    split <;> exact emu0
  obtain ⟨enc, boundary⟩ := entry_prefetch_boundary real source fetched _ pins core.v1.gic run emuFinal
  have fetchedPins := EntryClassNext.fetched_steppins acc (translateCurrent out) source fetched
    core.v1.pins regs
  have input := fetched_input acc (translateCurrent out) source fetched pins.el regs
  have quiet : HookQuiet ((budget - (k + 1)) + 1) source := by
    have equal : budget - (k + 1) + 1 = budget - k := by omega
    rw [equal]
    exact core.v1.quiet
  obtain ⟨guard, fetchedQuiet, it, ss⟩ :=
    fetched_rest acc (translateCurrent out) source fetched _ pins quiet regs
  have tailRun : nativeTail real source word' enc fetched = .ok () fin := boundary.symm.trans stepRun
  refine ⟨fetched,enc,fetchedPins,input,guard,fetchedQuiet,it,ss,tailRun,?_,⟨acc,translateCurrent out,regs⟩⟩
  simpa only [Nat.add_zero] using choice_delta_trans
    (NativeTagCheck.before_fetch_choice source) fetchChoice

#print axioms fields_of_frames
#print axioms native_class
#print axioms fetched_of_step
end DitShim243.ShimABI
