-- (H-P4 + D180a, /): PSTATE.DIT across one actual heap-v2 step.
-- Per-layer DIT carries (fetch: fetched_field; PMU spec hook: E20 frame; metadata: actionState; action:
-- Frame.pse with writes.dit = false, ActFrameBr.pse; epilogue: NonProjRegsEq keeps PSTATE.DIT), the
-- fetched-state bundle DitFetched, and entry_dit: the actual fetch + any tail that keeps DIT gives
-- ∃ fin, modelStep s = ok fin ∧ DIT fin = DIT s. Converters: dit_class (ClassTailAt), dit_mem (MemTailVAt
-- over Memory's FetchedCtx).
import HeapV2StepCerts.MemNextV3
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
open HeapV2StepCerts HeapV2StepCerts.MemNext
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace RtDit

theorem e20_dit (fetched sp : NativeState) (budget : Nat) (quiet : HookQuiet (budget + 1) fetched)
    (hook : (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp) :
    sp.regs.PSTATE.DIT = fetched.regs.PSTATE.DIT :=
  frame_pres_E20 (fun x => x.PSTATE.DIT) (fun x => by simp only [eraseE20])
    (entry_spec_post fetched sp (budget + 1) quiet hook).frame

theorem action_dit (w : BitVec 32) (sp : NativeState) (K : Int) :
    (actionState w sp K).regs.PSTATE.DIT = sp.regs.PSTATE.DIT := rfl

theorem frame_dit {writes : NativeEntry.Effects.Writes} {t u : NativeState}
    (h : NativeEntryContract.Frame writes t u) (hw : writes.dit = false) :
    u.regs.PSTATE.DIT = t.regs.PSTATE.DIT := by
  have e := congrArg ProcState.DIT h.pse
  simpa [NativeEntryContract.erasePState, hw] using e

theorem np_dit {r r' : Regs} (h : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap r r') :
    r'.PSTATE.DIT = r.PSTATE.DIT := by
  have e := congrArg (fun q : Regs => q.PSTATE.DIT) h
  simpa [ArmCertCT.CT2.mask, ArmCertCT.CT2.maskPSTATE] using e

/-- PMU hook, metadata, a writes-frame action not writing DIT, then the NonProj epilogue. -/
theorem tail_dit (fetched sp a fin : NativeState) (budget : Nat) (quiet : HookQuiet (budget + 1) fetched)
    (hook : (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp)
    {writes : NativeEntry.Effects.Writes} (w : BitVec 32) (K : Int)
    (frame : NativeEntryContract.Frame writes (actionState w sp K) a) (hw : writes.dit = false)
    (np : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs) :
    fin.regs.PSTATE.DIT = fetched.regs.PSTATE.DIT :=
  (np_dit np).trans ((frame_dit frame hw).trans ((action_dit w sp K).trans (e20_dit fetched sp budget quiet hook)))

/-- What a tail may use at the post-fetch state. -/
structure DitFetched {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (s final : NativeState) (budget : Nat) : Prop where
  pins : StepPins final
  input : NativeEntryInput.Input s final
  guard : MetadataGuard final
  quiet : HookQuiet (budget + 1) final
  it : final.regs.ShouldAdvanceIT = false
  ss : final.regs.ShouldAdvanceSS = true
  current : CurrentS1At spec config rows final
  closed : ClosedMembershipAt spec config rows mapping m final
  mem : final.mem = s.mem
  regs : ∃ (acc : AccessDescriptor) (nx : TTWState), final.regs = FetchedRegs acc nx s

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.entry_dit"
  (← IO.getStderr).flush

set_option maxHeartbeats 200000 in
/-- The actual step keeps PSTATE.DIT whenever the instruction tail does (fetch keeps it). -/
theorem entry_dit (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (w : BitVec 32) (s : NativeState) (stepPins : StepPins s)
    (hGIC : s.regs.bank_Option_InterruptID .__GIC_Pending = none)
    (features : EntryFeatures s.regs) (debug : E11Debug.E11CheckDebug s.regs)
    (budget : Nat) (quiet : HookQuiet (budget + 1) s)
    (base offset : BitVec 64) (placed : s.regs._PC = base + offset)
    (page : base.toNat % 4096 = 0) (word : offset.toNat % 4 = 0)
    (current : CurrentS1At spec config rows (ArmBridge.CruxGenGuarded.beforeFetchState s))
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (closed : ClosedMembershipAt spec config rows mapping m (ArmBridge.CruxGenGuarded.beforeFetchState s))
    (rawS : RawImageAt spec.imageRows s.mem)
    (noUpdS : ∀ (wr : Bool) (acc : AccessDescriptor), DataShape wr acc →
      NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (ob : FetchObligations spec config rows mapping w s)
    (tail : ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m s final budget →
      ∃ fin, nativeTail real s w enc0 final = .ok () fin ∧ fin.regs.PSTATE.DIT = final.regs.PSTATE.DIT) :
    ∃ fin, modelStep real s = .ok () fin ∧ fin.regs.PSTATE.DIT = s.regs.PSTATE.DIT := by
  have pins := NativeEntryTail.EntryPins.of_scalar s stepPins
  obtain ⟨step, el, il, _pc, emu0, e11, mode, spe⟩ := before_fetch_facts s pins features debug
  obtain ⟨acc, w', final, address, faultOut, translated, data, actualAcc, run, clean, bytes, fregs,
      fmem, _fev, curFinal, _, _info, _walk, _leaf, _middle, _len, _traffic, _tev, noUpdCond⟩ :=
    native_fetch_current_preserving_events spec config rows mapping (ArmBridge.CruxGenGuarded.beforeFetchState s)
      step el (pc_low_of_placement _ base offset placed page word) il current mode step.b0
      ⟨e11.mde, e11.hde⟩ spe ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc
  have hw := ob.code acc data.leafLevel data.view faultOut address translated w' clean bytes
  subst hw
  have closedFinal := closed_membership_after_fetch closed clean fregs
  obtain ⟨_, out, _, _, _, _, _, _, _, _, _, _, _, translatedRegs, _⟩ := clean
  have hregs : final.regs = FetchedRegs acc (translateCurrent out) s := by
    rw [fregs, translatedRegs, ob.rawOf acc]; rfl
  have emuFinal : final.regs.__emulator_termination_opcode = none := by
    rw [hregs]; unfold FetchedRegs fetchGuardRegs; split
    · exact emu0
    · exact emu0
  obtain ⟨enc0, hstep⟩ := entry_prefetch_boundary real s final _ pins hGIC run emuFinal
  have fpins := EntryClassNext.fetched_steppins acc (translateCurrent out) s final stepPins hregs
  have finput := fetched_input acc (translateCurrent out) s final pins.el hregs
  obtain ⟨guard, fquiet, it, ss⟩ :=
    fetched_rest acc (translateCurrent out) s final (budget + 1) pins quiet hregs
  have memNoUpd : translated.mem = (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState s)).mem :=
    (noUpdCond rawS (by
      rw [ob.rawOf acc]
      exact HeapV2StepCerts.RawFetch.noUpd_read noUpdS acc (actual_ifetch_flags actualAcc).2.2.1)).2.2
  have finalMem : final.mem = s.mem := fmem.trans memNoUpd
  have ditFinal : final.regs.PSTATE.DIT = s.regs.PSTATE.DIT := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.PSTATE.DIT) _ _ s (fun _ _ => rfl)
      (fun _ => rfl) rfl
  obtain ⟨fin, tailRun, dit⟩ := tail final enc0
    ⟨fpins, finput, guard, fquiet, it, ss, curFinal, closedFinal, finalMem, ⟨acc, _, hregs⟩⟩
  exact ⟨fin, hstep.trans tailRun, dit.trans ditFinal⟩

/-- Class converter: a ClassTailAt whose writes do not touch DIT. -/
theorem dit_class (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {budget : Nat}
    {w : BitVec 32} {writes : NativeEntry.Effects.Writes} {K : Int} {s : NativeState} {next : BitVec 64}
    (tail : ClassTailAt real w writes K s next) (hw : writes.dit = false) :
    ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m s final budget →
      ∃ fin, nativeTail real s w enc0 final = .ok () fin ∧ fin.regs.PSTATE.DIT = final.regs.PSTATE.DIT := by
  intro final enc0 f
  obtain ⟨sp, a, fin, hook, run, frame, _, _, _, _, _, _, np⟩ :=
    tail final enc0 budget f.pins f.input f.guard f.quiet f.it f.ss
  exact ⟨fin, run, tail_dit final sp a fin budget f.quiet hook w K frame hw np⟩

/-- Value-carrying class converter (Core's ClassTailVAt). -/
theorem dit_classV (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {budget : Nat}
    {w : BitVec 32} {writes : NativeEntry.Effects.Writes} {K : Int} {s : NativeState} {next : BitVec 64}
    {us : List (RegBind.Reg × RegBind.Upd)}
    (tail : RegVal.ClassTailVAt real w writes K s next us) (hw : writes.dit = false) :
    ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m s final budget →
      ∃ fin, nativeTail real s w enc0 final = .ok () fin ∧ fin.regs.PSTATE.DIT = final.regs.PSTATE.DIT := by
  intro final enc0 f
  obtain ⟨sp, a, fin, hook, run, frame, _, _, _, _, _, _, np, _⟩ :=
    tail final enc0 budget f.pins f.input f.guard f.quiet f.it f.ss
  exact ⟨fin, run, tail_dit final sp a fin budget f.quiet hook w K frame hw np⟩

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.dit_mem"
  (← IO.getStderr).flush

/-- Memory converter: Memory's MemTailVAt over FetchedCtx, the context rebuilt at the fetched state. -/
theorem dit_mem (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {budget : Nat}
    {p : HeapV2E17.Pins} {k : Nat} {D : Nat → Prop}
    {w : BitVec 32} {writes : NativeEntry.Effects.Writes} {K : Int} {s : NativeState} {next : BitVec 64}
    {us : List (RegBind.Reg × RegBind.Upd)}
    (tail : MemTailVAt real spec config rows (FetchedCtx spec config rows mapping m p k) D w writes K s next us)
    (hw : writes.dit = false)
    (rawS : RawImageAt spec.imageRows s.mem)
    (noUpdS : ∀ (wr : Bool) (acc : AccessDescriptor), DataShape wr acc →
      NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (regBindS : RegBind.RegBind p k s) (presentS : C3.DataPresent p mapping s)
    (post2S : MemM1.MemReadD2.PostRegs2 s.regs) (modeS : HostEL0ModeAt s.regs)
    (edebugS : ExistingE11DebugAt s.regs)
    (featS : s.regs.FeatureImpl[7] = true ∧ s.regs.FeatureImpl[3] = false ∧
      s.regs.FeatureImpl[227] = false ∧ s.regs.FeatureImpl[111] = true)
    (dcacheS : currentDCache s.regs = true) :
    ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m s final budget →
      ∃ fin, nativeTail real s w enc0 final = .ok () fin ∧ fin.regs.PSTATE.DIT = final.regs.PSTATE.DIT := by
  intro final enc0 f
  obtain ⟨acc, nx, hregs⟩ := f.regs
  have gprFinal : final.regs.gpr = s.regs.gpr := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.gpr) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have spFinal : final.regs.SP_EL0 = s.regs.SP_EL0 := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.SP_EL0) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have sysF : SysEq2 s.regs final.regs := EntryBranchPins.sysEq2_symm _ _ f.input.sys
  have ctx : FetchedCtx spec config rows mapping m p k final :=
    { closed := f.closed
      regBind := C3.regBind_of_regs gprFinal spFinal regBindS
      present := C3.DataPresent.carry (fun a h => by rw [f.mem]; exact h) presentS
      raw := by rw [f.mem]; exact rawS
      noUpd := fun wr acc hs => by rw [hostHAFT_eq sysF]; exact noUpdS wr acc hs
      post2 := HeapV2StepCerts.MemConfigFrame.post2 sysF.feat sysF.el sysF.nrw sysF.scr sysF.hcr sysF.sctlr sysF.spe post2S
      mode := HeapV2StepCerts.MemConfigFrame.mode sysF.feat sysF.el sysF.scr sysF.hcr modeS
      debug := HeapV2StepCerts.MemConfigFrame.debug sysF.mdscr sysF.hde edebugS
      feat := by rw [sysF.feat]; exact featS
      dcache := HeapV2StepCerts.MemConfigFrame.dcache sysF.sctlr dcacheS }
  obtain ⟨sp, a, fin, _, hook, run, frame, _, _, _, _, _, _, _, _, np, _, _⟩ :=
    tail final enc0 budget f.pins f.input f.guard f.quiet f.it f.ss f.current ctx
  exact ⟨fin, run, tail_dit final sp a fin budget f.quiet hook w K frame hw np⟩

#print axioms e20_dit
#print axioms frame_dit
#print axioms np_dit
#print axioms entry_dit
#print axioms dit_class
#print axioms dit_classV
#print axioms dit_mem
end RtDit
