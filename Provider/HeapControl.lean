-- Translation controls and descriptor bytes through actual heap continuations.
import RtPremC.CtlM
import TagCheckFrames.Fetch
import NativeTagCheck.BeforeFetch

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
open HeapV2StepCerts CertiFFI.Prog.Generic.ModelRunView
open RtPremC RtDit
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.ClosedChain
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2
open ArmBridge.CruxGenGuarded.ChainInvV3
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 1024
set_option profiler true
set_option profiler.threshold 1000

namespace ReleaseProfile.HeapControl

#check "CURRENT_DECL heap actual control entry"
theorem entry (real : Type) [Sail.SailReal real]
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
      NativeMteTagCheck.ChoiceDelta s final 0 → ∃ fin, nativeTail real s w enc0 final = .ok () fin ∧ CtlRel spec final fin) :
    ∃ fin, modelStep real s = .ok () fin ∧ CtlRel spec s fin := by
  have pins := NativeEntryTail.EntryPins.of_scalar s stepPins
  obtain ⟨step, el, il, _pc, emu0, e11, mode, spe⟩ := before_fetch_facts s pins features debug
  obtain ⟨acc, w', final, address, faultOut, translated, data, actualAcc, run, clean, bytes, fregs,
      fmem, _fev, curFinal, _, fetchChoice, _info, _walk, _leaf, _middle, _len, _traffic, _tev, noUpdCond⟩ :=
    native_fetch_current_preserving_events_choice spec config rows mapping (ArmBridge.CruxGenGuarded.beforeFetchState s)
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
  have choice : NativeMteTagCheck.ChoiceDelta s final 0 := by
    simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans
      (NativeTagCheck.before_fetch_choice s) fetchChoice
  obtain ⟨fin, tailRun, rel⟩ := tail final enc0
    ⟨fpins, finput, guard, fquiet, it, ss, curFinal, closedFinal, finalMem, ⟨acc, _, hregs⟩⟩ choice
  exact ⟨fin, hstep.trans tailRun, (CtlRel.of_mem ctlFinal finalMem).trans rel⟩

#check "CURRENT_DECL actual fetch source and counter"
theorem fetch_choice (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (word : BitVec 32) (source final : NativeState) (stepPins : StepPins source)
    (features : EntryFeatures source.regs) (debug : E11Debug.E11CheckDebug source.regs)
    (base offset : BitVec 64) (placed : source.regs._PC = base + offset)
    (page : base.toNat % 4096 = 0) (aligned : offset.toNat % 4 = 0)
    (current : CurrentS1At spec config rows (beforeFetchState source))
    (ob : FetchObligations spec config rows mapping word source)
    (run : ∃ value, __FetchInstr (beforeFetchState source).regs._PC (beforeFetchState source) = .ok value final) :
    NativeMteTagCheck.ChoiceDelta source final 0 := by
  have pins := NativeEntryTail.EntryPins.of_scalar source stepPins
  obtain ⟨step, el, il, _pc, _emu0, e11, mode, spe⟩ := before_fetch_facts source pins features debug
  obtain ⟨acc, word', fetched, address, faultOut, translated, data, actualAcc, actual,
      clean, bytes, fregs, fmem, fev, curFinal, rest, fetchChoice,
      info, walk, leaf, middle, length, traffic, endEv, noUpd⟩ :=
    native_fetch_current_preserving_events_choice spec config rows mapping (beforeFetchState source)
      step el (pc_low_of_placement _ base offset placed page aligned) il current mode step.b0
      ⟨e11.mde, e11.hde⟩ spe ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc
  obtain ⟨value, supplied⟩ := run
  have same : fetched = final := (EStateM.Result.ok.inj (actual.symm.trans supplied)).2
  rw [← same]
  simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans
    (NativeTagCheck.before_fetch_choice source) fetchChoice

#check "CURRENT_DECL heap memory control frame"
theorem memory_frame {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (fetched sp action fin : NativeState) (budget : Nat) (quiet : HookQuiet (budget + 1) fetched)
    (hook : (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp)
    {writes : NativeEntry.Effects.Writes} (word : BitVec 32) (K : Int)
    (frame : NativeEntryContract.Frame writes (actionState word sp K) action)
    (epilogue : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap action.regs fin.regs)
    (written : Nat → Prop)
    (memory : WritesOnly written (fun a => fetched.mem[a]?) (fun a => fin.mem[a]?))
    (separated : Separated (rowsFootprint spec.imageRows).byte written) :
    RtPremC.CtlRel spec fetched fin := by
  refine ⟨RtPremC.tail_ctl fetched sp action fin budget quiet hook word K frame epilogue, ?_⟩
  intro address descriptor
  exact memory address (fun changed => separated address descriptor changed)

#check "CURRENT_DECL heap scalar control tail"
theorem scalar_tail (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {budget : Nat}
    {word : BitVec 32} {writes : NativeEntry.Effects.Writes} {K : Int} {source : NativeState}
    {next : BitVec 64} (tail : ClassTailAt real word writes K source next) :
    ∀ fetched enc, RtDit.DitFetched spec config rows mapping m source fetched budget →
      ∃ fin, nativeTail real source word enc fetched = .ok () fin ∧ RtPremC.CtlRel spec fetched fin := by
  intro fetched enc context
  obtain ⟨sp, action, fin, hook, run, frame, _, _, _, memory, _, _, epilogue⟩ :=
    tail fetched enc budget context.pins context.input context.guard context.quiet context.it context.ss
  exact ⟨fin,run,RtPremC.CtlRel.of_mem
    (RtPremC.tail_ctl fetched sp action fin budget context.quiet hook word K frame epilogue) memory⟩

#check "CURRENT_DECL heap control prefix composition"
theorem through_prefix (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain) (entry : NativeState) (length : Nat)
    (Inv : Nat → NativeState → Prop)
    (invariant : ∀ k, k < length → Inv k (stateAt real entry k))
    (steps : ∀ k, k < length → ∀ state, Inv k state →
      ∃ next, modelStep real state = .ok () next ∧ RtPremC.CtlRel spec state next) :
    ∀ k, k ≤ length → RtPremC.CtlRel spec entry (stateAt real entry k) := by
  intro k bound
  induction k with
  | zero => exact RtPremC.CtlRel.refl spec entry
  | succ k prior =>
    obtain ⟨next,run,control⟩ := steps k (by omega) _ (invariant k (by omega))
    rw [RtDit.stateAt_succ_of run]
    exact (prior (by omega)).trans control

#print axioms entry
#print axioms fetch_choice
#print axioms memory_frame
#print axioms scalar_tail
#print axioms through_prefix
end ReleaseProfile.HeapControl
