-- RtPremC.CtlM (, premise C): one actual heap-v2 step keeps the translation-control
-- vector (ctlv) and the descriptor-footprint bytes. Same per-kind shape as LRDit2's dit_*M (identical
-- argument lists, so the generated DitSegM_* segments retarget by renaming).
import RtPremC.Ctl
import Bridge.CruxGenGuarded.EntryCallerFrames
import NativeEntryCallerTransport.Fields
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
open ArmBridge.CruxGenGuarded.ChainInvV4 HeapV2StepCerts HeapV2StepCerts.E17General HeapV2StepCerts.MemNext
open NativeEntryCallerParts
open RtDit (DitFetched)
open ArmBridge.CruxGenGuarded.CallerBl NativeEntryCallerTransport ArmFull.Register ArmBridge.CruxGen
open NativeEntryTail (EntryPins)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false
namespace RtPremC

/-- Control vector equal and descriptor-footprint bytes equal. -/
def CtlRel {domain : QueryDomain} (spec : TopologyImageSpec domain) (s f : NativeState) : Prop :=
  ctlv f.regs = ctlv s.regs ∧ ∀ a, (rowsFootprint spec.imageRows).byte a → f.mem[a]? = s.mem[a]?

theorem CtlRel.refl {domain : QueryDomain} (spec : TopologyImageSpec domain) (s : NativeState) : CtlRel spec s s :=
  ⟨rfl, fun _ _ => rfl⟩

theorem CtlRel.trans {domain : QueryDomain} {spec : TopologyImageSpec domain} {a b c : NativeState}
    (h1 : CtlRel spec a b) (h2 : CtlRel spec b c) : CtlRel spec a c :=
  ⟨h2.1.trans h1.1, fun x hx => (h2.2 x hx).trans (h1.2 x hx)⟩

theorem CtlRel.of_mem {domain : QueryDomain} {spec : TopologyImageSpec domain} {s f : NativeState}
    (r : ctlv f.regs = ctlv s.regs) (m : f.mem = s.mem) : CtlRel spec s f := ⟨r, fun _ _ => by rw [m]⟩

/-- PMU hook, metadata, a writes-frame action, then the NonProj epilogue. -/
theorem tail_ctl (fetched sp a fin : NativeState) (budget : Nat) (quiet : HookQuiet (budget + 1) fetched)
    (hook : (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp)
    {writes : NativeEntry.Effects.Writes} (w : BitVec 32) (K : Int)
    (frame : NativeEntryContract.Frame writes (actionState w sp K) a)
    (np : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs) :
    ctlv fin.regs = ctlv fetched.regs :=
  (ctl_np np).trans ((ctl_frame frame).trans ((ctl_action w sp K).trans (ctl_e20 fetched sp budget quiet hook)))

theorem tailBr_ctl (fetched sp a fin : NativeState) (budget : Nat) (quiet : HookQuiet (budget + 1) fetched)
    (hook : (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp) (w : BitVec 32) (K : Int)
    (frame : ArmBridge.CruxGenBr.ActFrameBr (actionState w sp K) a)
    (np : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs) :
    ctlv fin.regs = ctlv fetched.regs :=
  (ctl_np np).trans ((ctl_frameBr frame).trans ((ctl_action w sp K).trans (ctl_e20 fetched sp budget quiet hook)))

def CtlStepM (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget k : Nat) : Prop :=
  ∀ x, I4 spec config rows mapping base pins entry budget k x →
    ∃ fin, modelStep real x = .ok () fin ∧ CtlRel spec x fin

set_option maxHeartbeats 400000 in
theorem entry_ctlM (real : Type) [Sail.SailReal real]
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
      ∃ fin, nativeTail real s w enc0 final = .ok () fin ∧ CtlRel spec final fin) :
    ∃ fin, modelStep real s = .ok () fin ∧ CtlRel spec s fin := by
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
  have ctlFinal : ctlv final.regs = ctlv s.regs := by rw [hregs]; exact ctl_fetched acc _ s
  obtain ⟨fin, tailRun, rel⟩ := tail final enc0
    ⟨fpins, finput, guard, fquiet, it, ss, curFinal, closedFinal, finalMem, ⟨acc, _, hregs⟩⟩
  exact ⟨fin, hstep.trans tailRun, (CtlRel.of_mem ctlFinal finalMem).trans rel⟩

theorem ctl_atM (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (x : NativeState)
    (inv : ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x)
    (ob : FetchObligations spec config rows mapping w x) (_D : Nat → Prop)
    (tail : ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m x final (budget - (k + 1)) →
      ∃ fin, nativeTail real x w enc0 final = .ok () fin ∧ CtlRel spec final fin) :
    ∃ fin, modelStep real x = .ok () fin ∧ CtlRel spec x fin := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  exact entry_ctlM real spec config rows mapping w x inv.v2.v1.pins inv.v2.v1.gic inv.v2.v1.features inv.v2.v1.debug
    (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned inv.v2.v1.current m inv.v2.closed inv.raw
    inv.noUpd ob tail

theorem ctl_classM (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {budget : Nat}
    {w : BitVec 32} {writes : NativeEntry.Effects.Writes} {K : Int} {s : NativeState} {next : BitVec 64}
    (tail : ClassTailAt real w writes K s next) (_hw : writes.dit = false) (_D : Nat → Prop) :
    ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m s final budget →
      ∃ fin, nativeTail real s w enc0 final = .ok () fin ∧ CtlRel spec final fin := by
  intro final enc0 f
  obtain ⟨sp, a, fin, hook, run, frame, _, _, _, mem, _, _, np⟩ :=
    tail final enc0 budget f.pins f.input f.guard f.quiet f.it f.ss
  exact ⟨fin, run, CtlRel.of_mem (tail_ctl final sp a fin budget f.quiet hook w K frame np) mem⟩

theorem ctl_memM (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {budget : Nat}
    {p : HeapV2E17.Pins} {k : Nat} {D : Nat → Prop}
    {w : BitVec 32} {writes : NativeEntry.Effects.Writes} {K : Int} {s : NativeState} {next : BitVec 64}
    {us : List (RegBind.Reg × RegBind.Upd)}
    (tail : MemTailVAt real spec config rows (FetchedCtx spec config rows mapping m p k) D w writes K s next us)
    (_hw : writes.dit = false)
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
      ∃ fin, nativeTail real s w enc0 final = .ok () fin ∧ CtlRel spec final fin := by
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
  obtain ⟨sp, a, fin, written, hook, run, frame, _, _, _, wo, sep, _, _, _, np, _, _⟩ :=
    tail final enc0 budget f.pins f.input f.guard f.quiet f.it f.ss f.current ctx
  exact ⟨fin, run, tail_ctl final sp a fin budget f.quiet hook w K frame np,
    fun x hx => wo x (sep x hx)⟩

theorem ctl_cbzM (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {budget : Nat} {s : NativeState}
    (Rt : BitVec 5) (imm19 : BitVec 19)
    (noEret : (Sail.BitVec.extractLsb (EntryBodyCbz.W Rt imm19) 31 12 == 879088#20) = false)
    (stepPins : StepPins s) (bp : Crypto.BranchV2.BranchPinsV2PA s)
    (_D : Nat → Prop) (hlow : (s.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55) :
    ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m s final budget →
      ∃ fin, nativeTail real s (EntryBodyCbz.W Rt imm19) enc0 final = .ok () fin ∧ CtlRel spec final fin := by
  intro final enc0 f
  obtain ⟨acc, nx, hregs⟩ := f.regs
  have bpF := EntryFetchedBranch.fetched_branch_pins acc nx s final stepPins hregs bp
  obtain ⟨sp, a, fin, pmu, run, frame, _, _, _, _, mem, _, _, _, _, _, np, _⟩ :=
    EntryBodyCbz.native_tail_x real s final enc0 Rt imm19 noEret f.pins bpF f.input f.guard budget f.quiet f.it f.ss hlow
  exact ⟨fin, run, CtlRel.of_mem (tailBr_ctl final sp a fin budget f.quiet pmu _ _ frame np) mem⟩

theorem ctl_bcondM (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {budget : Nat} {s : NativeState}
    (cond : BitVec 4) (imm19 : BitVec 19)
    (noEret : (Sail.BitVec.extractLsb (EntryBodyBcond.W cond imm19) 31 12 == 879088#20) = false)
    (stepPins : StepPins s) (bp : Crypto.BranchV2.BranchPinsV2PA s)
    (_D : Nat → Prop) (hlow : (s.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55) :
    ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m s final budget →
      ∃ fin, nativeTail real s (EntryBodyBcond.W cond imm19) enc0 final = .ok () fin ∧ CtlRel spec final fin := by
  intro final enc0 f
  obtain ⟨acc, nx, hregs⟩ := f.regs
  have bpF := EntryFetchedBranch.fetched_branch_pins acc nx s final stepPins hregs bp
  obtain ⟨sp, a, fin, pmu, run, frame, _, _, _, _, mem, _, _, _, _, _, np, _⟩ :=
    EntryBodyBcond.native_tail_x real s final enc0 cond imm19 noEret f.pins bpF f.input f.guard budget f.quiet f.it f.ss hlow
  exact ⟨fin, run, CtlRel.of_mem (tailBr_ctl final sp a fin budget f.quiet pmu _ _ frame np) mem⟩

theorem ctl_retM (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {budget : Nat} {s : NativeState}
    (Rn : BitVec 5) (hRn : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (EntryBodyRet.W Rn) 31 12 == 879088#20) = false)
    (stepPins : StepPins s) (bp : Crypto.BranchV2.BranchPinsV2PA s)
    (_D : Nat → Prop) (hlow : (s.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55) :
    ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m s final budget →
      ∃ fin, nativeTail real s (EntryBodyRet.W Rn) enc0 final = .ok () fin ∧ CtlRel spec final fin := by
  intro final enc0 f
  obtain ⟨acc, nx, hregs⟩ := f.regs
  have bpF := EntryFetchedBranch.fetched_branch_pins acc nx s final stepPins hregs bp
  obtain ⟨sp, a, fin, pmu, run, frame, _, _, _, _, mem, _, _, _, _, _, np, _⟩ :=
    EntryBodyRet.native_tail_x real s final enc0 Rn hRn noEret f.pins bpF f.input f.guard budget f.quiet f.it f.ss hlow
  exact ⟨fin, run, CtlRel.of_mem (tailBr_ctl final sp a fin budget f.quiet pmu _ _ frame np) mem⟩

theorem ctl_blAction (imm26 : BitVec 26) (s : NativeState) : ctlv (blActionState imm26 s).regs = ctlv s.regs := by
  have sy := ArmBridge.CruxGenGuarded.bl_action_sys imm26 s
  have hp := NativeEntryCallerParts.bl_action_PSTATE imm26 s
  simp only [ctlv, NativeEntryCallerTransport.bl_FeatureImpl, NativeEntryCallerTransport.bl_bank_BitVec_64,
    NativeEntryCallerTransport.bl_bank_BitVec_128, NativeEntryCallerTransport.bl_bank_Int, hp, sy.tlb]

theorem ctl_blM (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {budget : Nat} {s : NativeState}
    (imm26 : BitVec 26) (controls : CallerControls s) (low : (blTarget imm26 s).toNat < 2 ^ 55) (_D : Nat → Prop) :
    ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m s final budget →
      ∃ fin, nativeTail real s (NativeEntryCallerDispatch.Bl.word imm26) enc0 final = .ok () fin ∧ CtlRel spec final fin := by
  intro final enc0 f
  obtain ⟨acc, nx, hregs⟩ := f.regs
  have sysF : SysEq2 s.regs final.regs := EntryBranchPins.sysEq2_symm _ _ f.input.sys
  have controlsF := HeapV2StepCerts.BlStepV3.caller_controls_fetched s final hregs sysF controls
  have pinsE : EntryPins final := NativeEntryTail.EntryPins.of_scalar final f.pins
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule (budget + 1) final f.quiet
  have ps := NativeEntryTail.EntryPins.after_E20 final sp pinsE post.frame
  have pc := caller_controls_after_E20 final sp controlsF post.frame
  let a := actionState (NativeEntryCallerDispatch.Bl.word imm26) sp 68
  have ca : CallerControls a := caller_controls_at_metadata sp (NativeEntryCallerDispatch.Bl.word imm26) 68 pc
  have pa : EntryPins a := entryPins_at_metadata sp (NativeEntryCallerDispatch.Bl.word imm26) 68 ps
  have qa : HookQuiet (budget + 1) a := actionState_quiet (NativeEntryCallerDispatch.Bl.word imm26) sp 68 (budget + 1) post.quiet
  have target : blTarget imm26 a = blTarget imm26 s := by
    rw [NativeEntryCallerRegisters.bl_target, NativeEntryCallerRegisters.bl_target]
    change sp.regs._PC + _ = s.regs._PC + _
    rw [(PMUFrame.of_E20 post.frame).pc, f.input.pc]
  have lowA : (blTarget imm26 a).toNat < 2^55 := by rw [target]; exact low
  have encA : a.regs.__ThisInstrEnc = .__A64 := by rfl
  have eretA : (Sail.BitVec.extractLsb (a.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false :=
    word_not_eret imm26
  have itA : a.regs.ShouldAdvanceIT = false := (PMUFrame.of_E20 post.frame).it.trans f.it
  have ssA : a.regs.ShouldAdvanceSS = true := (PMUFrame.of_E20 post.frame).ss.trans f.ss
  have dispatch : DispatchAt real (NativeEntryCallerDispatch.Bl.word imm26) (decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 1#1) 68 := by
    intro pc t see
    exact NativeEntryCallerDispatch.Bl.dispatch_at real pc imm26 t (by simpa using see)
  have metadataBoundary := metadata_boundary_at real s (NativeEntryCallerDispatch.Bl.word imm26) (decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 1#1) enc0 sp
    (f.guard.after_E20 post.frame) 68 (by decide) dispatch
  obtain ⟨fin, run, _, _, _, _, _, _, _, _, _, _, _, mem, _, _, np⟩ :=
    bl_action_tail real s (NativeEntryCallerDispatch.Bl.word imm26) enc0 imm26 a budget ca lowA qa pa encA eretA itA ssA
  refine ⟨fin, (spec_pmu_boundary real s (NativeEntryCallerDispatch.Bl.word imm26) enc0 final sp hook).trans (metadataBoundary.trans run),
    CtlRel.of_mem ?_ (mem.trans ((actionState_mem (NativeEntryCallerDispatch.Bl.word imm26) sp 68).trans post.mem))⟩
  exact (ctl_np np).trans ((ctl_blAction imm26 a).trans ((ctl_action _ sp 68).trans (ctl_e20 final sp budget f.quiet hook)))

#print axioms entry_ctlM
#print axioms ctl_classM
#print axioms ctl_memM
#print axioms ctl_cbzM
#print axioms ctl_bcondM
#print axioms ctl_retM
#print axioms ctl_blAction
#print axioms ctl_blM
end RtPremC
