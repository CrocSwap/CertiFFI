-- (H-P13 → Release.ShimPrologue/ShimEpilogue, certiffi e4953b32): event shapes and E17 at shim
-- states. entry_genE = the actual fetch + any tail fact, exporting the fetch run; evShape_of_fetchRunD = Core's
-- fetch_records + a tail that appends D with records `data` (StepEvents.EvShape spec mapping data x fin);
-- shim_ev over ShimInv; per-kind tails (event-silent: BTI c, Core class E-tails, MRS/MSR DIT, DIT on, ISB, BL, RET;
-- data: STP/LDP slot via Memory's MemTailE with prem_shimStp/Ldp); e17_of_shimInv (state_facts + closed).
import RtDit2.ShimDit
import RtB4.EvShapeBridge
import RtB6.RichZ
import HeapV2StepCerts.MemTailDE
import HeapV2StepCerts.RegValE
import HeapV2StepCerts.FetchTiming
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
open HeapV2StepCerts HeapV2StepCerts.MemNext NativeEntryCallerParts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option Elab.async false
namespace RtDit.ShimEv
open RtDit RtDit.Shim

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.ShimEv.entry_genE"
  (← IO.getStderr).flush

theorem entry_genE (real : Type) [Sail.SailReal real]
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
    (ob : FetchObligations spec config rows mapping w s) (Q : NativeState → NativeState → Prop)
    (tail : ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m s final budget →
      ∃ fin, nativeTail real s w enc0 final = .ok () fin ∧ Q final fin) :
    ∃ final fin, modelStep real s = .ok () fin ∧
      __FetchInstr (ArmBridge.CruxGenGuarded.beforeFetchState s).regs._PC (ArmBridge.CruxGenGuarded.beforeFetchState s) =
        .ok (__InstrEnc.__A64, w) final ∧ Q final fin := by
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
  have gprFinal : final.regs.gpr = s.regs.gpr := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.gpr) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have spFinal : final.regs.SP_EL0 = s.regs.SP_EL0 := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.SP_EL0) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  obtain ⟨fin, tailRun, q⟩ := tail final enc0
    ⟨fpins, finput, guard, fquiet, it, ss, curFinal, closedFinal, finalMem, ⟨acc, _, hregs⟩⟩
  exact ⟨final, fin, hstep.trans tailRun, run, q⟩


/-- EvShape from the fetch run and a tail appending D with records `data`. -/
theorem evShape_of_fetchRunD {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (w : BitVec 32) (x fin : NativeState) (stepPins : StepPins x) (features : EntryFeatures x.regs)
    (debug : E11Debug.E11CheckDebug x.regs)
    (current : CurrentS1At spec config rows (beforeFetchState x))
    (pcLow : Sail.BitVec.extractLsb x.regs._PC 1 0 = 0#2)
    (ob : FetchObligations spec config rows mapping w x)
    (raw : RawImageAt spec.imageRows x.mem)
    (noUpd : ∀ (wr : Bool) (acc : AccessDescriptor), DataShape wr acc →
      NoUpdateRows {spec.params with haft := hostHAFT x.regs} acc spec.imageRows = true)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (data : List (Option ArmCertCTOrdered.OrderedEventV2.Record))
    (fetchRun : ∃ f w', __FetchInstr (beforeFetchState x).regs._PC (beforeFetchState x) =
      .ok (__InstrEnc.__A64, w') f ∧ ∃ D : Array Event, fin.events = f.events ++ D ∧
        D.toList.map ArmCertCTOrdered.OrderedEventV2.record = data) :
    StepEvents.EvShape spec mapping data x fin := by
  have pins := NativeEntryTail.EntryPins.of_scalar x stepPins
  obtain ⟨step, el, il, _pc, _emu0, e11, mode, spe⟩ := before_fetch_facts x pins features debug
  obtain ⟨_acc, word, final, n, T, _address, _faultOut, _translated, _data, _actual, frun, mapped, fev, ftr,
      -⟩ :=
    HeapV2StepCerts.FetchTiming.fetch_records spec config rows mapping (beforeFetchState x) step el pcLow il
      current mode step.b0 ⟨e11.mde, e11.hde⟩ spe ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc
      raw noUpd nodup
  obtain ⟨f, w', run, D, evs, recs⟩ := fetchRun
  rw [frun] at run
  have same : final = f := by
    injection run with h1 h2
  subst same
  refine ⟨n, T, D, ?_, ftr, mapped, recs⟩
  rw [evs, fev]
  rfl

/-- A ShimInv step whose tail appends D (records `data`) has EvShape data. -/
theorem shim_ev (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (w : BitVec 32) (x : NativeState)
    (inv : RtShim2.ShimInv spec config rows mapping m scope image loadBase base offset budget k x)
    (ob : FetchObligations spec config rows mapping w x) (data : List (Option ArmCertCTOrdered.OrderedEventV2.Record))
    (tail : ∀ (final : NativeState) (enc0 : __InstrEnc),
      DitFetched spec config rows mapping m x final (budget - (k + 1)) →
      ∃ fin, nativeTail real x w enc0 final = .ok () fin ∧ ∃ D : Array Event, fin.events = final.events ++ D ∧
        D.toList.map ArmCertCTOrdered.OrderedEventV2.record = data) :
    ∃ fin, modelStep real x = .ok () fin ∧ StepEvents.EvShape spec mapping data x fin := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨final, fin, run, frun, D, evs, recs⟩ :=
    entry_genE real spec config rows mapping w x inv.v2.v1.pins inv.v2.v1.gic inv.v2.v1.features inv.v2.v1.debug
      (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned inv.v2.v1.current m inv.v2.closed inv.raw
      inv.noUpd ob _ tail
  exact ⟨fin, run, evShape_of_fetchRunD spec config rows mapping w x fin inv.v2.v1.pins inv.v2.v1.features
    inv.v2.v1.debug inv.v2.v1.current (pc_low_of_placement _ base (offset k) inv.v2.v1.pc page aligned) ob inv.raw
    inv.noUpd nodup data ⟨final, w, frun, D, evs, recs⟩⟩

/-- Event-silent tails as D = #[]. -/
theorem silent {fin final : NativeState} (h : fin.events = final.events) :
    ∃ D : Array Event, fin.events = final.events ++ D ∧ D.toList.map ArmCertCTOrdered.OrderedEventV2.record = [] :=
  ⟨#[], by rw [h]; rfl, rfl⟩

/-- ISB SY's one ordered event: the barrier. -/
def isbData : List (Option ArmCertCTOrdered.OrderedEventV2.Record) :=
  [ArmCertCTOrdered.OrderedEventV2.record (Event.barrier (Barrier.Barrier_ISB ()))]

section
variable {real : Type} [Sail.SailReal real]
    {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {budget : Nat} {x : NativeState}

theorem tail_btiC : ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m x final budget →
    ∃ fin, nativeTail real x NativeEntryDispatch.BtiC.word enc0 final = .ok () fin ∧ ∃ D : Array Event,
      fin.events = final.events ++ D ∧ D.toList.map ArmCertCTOrdered.OrderedEventV2.record = [] := by
  intro final enc0 f
  obtain ⟨fin, run, _, _, _, _, _, ev, _⟩ :=
    NativeShimTails.btiC_fin real x final enc0 f.pins f.input f.guard budget f.quiet f.it f.ss
  exact ⟨fin, run, silent ev⟩

theorem tail_classE {w : BitVec 32} {writes : NativeEntry.Effects.Writes} {K : Int} {next : BitVec 64}
    {us : List (RegBind.Reg × RegBind.Upd)} (tail : RegValE.ClassTailVAt real w writes K x next us) :
    ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m x final budget →
    ∃ fin, nativeTail real x w enc0 final = .ok () fin ∧ ∃ D : Array Event,
      fin.events = final.events ++ D ∧ D.toList.map ArmCertCTOrdered.OrderedEventV2.record = [] := by
  intro final enc0 f
  obtain ⟨_, _, fin, _, run, _, _, _, _, _, _, _, _, ev, _⟩ :=
    tail final enc0 budget f.pins f.input f.guard f.quiet f.it f.ss
  exact ⟨fin, run, silent ev⟩

theorem tail_mrs9 (profile : NativeEntryAdapters.MrsDit.Profile x) :
    ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m x final budget →
    ∃ fin, nativeTail real x (NativeEntryDispatch.MrsDit.word 9#5) enc0 final = .ok () fin ∧ ∃ D : Array Event,
      fin.events = final.events ++ D ∧ D.toList.map ArmCertCTOrdered.OrderedEventV2.record = [] := by
  intro final enc0 f
  obtain ⟨_, _, fin, _, _, run, _, _, _, _, _, _, _, _, ev, _⟩ :=
    EntryMrsDit.native_tail real x final enc0 9#5 (by decide) profile f.pins f.input f.guard budget f.quiet f.it f.ss
  exact ⟨fin, run, silent ev⟩

theorem tail_msr9 (profile : NativeEntryAdapters.MsrDit.Profile x) :
    ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m x final budget →
    ∃ fin, nativeTail real x (NativeEntryDispatch.MsrDit.word 9#5) enc0 final = .ok () fin ∧ ∃ D : Array Event,
      fin.events = final.events ++ D ∧ D.toList.map ArmCertCTOrdered.OrderedEventV2.record = [] := by
  intro final enc0 f
  obtain ⟨_, _, fin, _, _, run, _, _, _, _, _, _, _, _, ev, _⟩ :=
    EntryMsrDit.native_tail real x final enc0 9#5 (by decide) profile f.pins f.input f.guard budget f.quiet f.it f.ss
  exact ⟨fin, run, silent ev⟩

theorem tail_ditOn (profile : NativeEntryAdapters.DitOn.Profile x) :
    ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m x final budget →
    ∃ fin, nativeTail real x NativeEntryDispatch.DitOn.word enc0 final = .ok () fin ∧ ∃ D : Array Event,
      fin.events = final.events ++ D ∧ D.toList.map ArmCertCTOrdered.OrderedEventV2.record = [] := by
  intro final enc0 f
  obtain ⟨_, _, fin, _, _, run, _, _, _, _, _, _, _, _, ev, _⟩ :=
    EntryDitOn.native_tail real x final enc0 profile f.pins f.input f.guard budget f.quiet f.it f.ss
  exact ⟨fin, run, silent ev⟩

theorem tail_isb (profile : NativeEntryAdapters.IsbSy.Profile x) :
    ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m x final budget →
    ∃ fin, nativeTail real x NativeEntryDispatch.IsbSy.word enc0 final = .ok () fin ∧ ∃ D : Array Event,
      fin.events = final.events ++ D ∧ D.toList.map ArmCertCTOrdered.OrderedEventV2.record = isbData := by
  intro final enc0 f
  obtain ⟨_, _, fin, _, _, run, _, _, _, _, _, _, _, _, ev, _⟩ :=
    EntryIsbSy.native_tail real x final enc0 profile f.pins f.input f.guard budget f.quiet f.it f.ss
  exact ⟨fin, run, #[Event.barrier (Barrier.Barrier_ISB ())], by rw [ev, Array.push_eq_append], rfl⟩

theorem tail_ret (Rn : BitVec 5) (hRn : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (EntryBodyRet.W Rn) 31 12 == 879088#20) = false)
    (stepPins : StepPins x) (bp : Crypto.BranchV2.BranchPinsV2PA x)
    (hlow : (x.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55) :
    ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m x final budget →
    ∃ fin, nativeTail real x (EntryBodyRet.W Rn) enc0 final = .ok () fin ∧ ∃ D : Array Event,
      fin.events = final.events ++ D ∧ D.toList.map ArmCertCTOrdered.OrderedEventV2.record = [] := by
  intro final enc0 f
  obtain ⟨acc, nx, hregs⟩ := f.regs
  have bpF := EntryFetchedBranch.fetched_branch_pins acc nx x final stepPins hregs bp
  obtain ⟨_, _, fin, _, run, _, _, _, _, _, _, ev, _⟩ :=
    EntryBodyRet.native_tail_x real x final enc0 Rn hRn noEret f.pins bpF f.input f.guard budget f.quiet f.it f.ss hlow
  exact ⟨fin, run, silent ev⟩

theorem tail_bl (imm26 : BitVec 26) (controls : CallerControls x) (low : (blTarget imm26 x).toNat < 2 ^ 55) :
    ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m x final budget →
    ∃ fin, nativeTail real x (NativeEntryCallerDispatch.Bl.word imm26) enc0 final = .ok () fin ∧ ∃ D : Array Event,
      fin.events = final.events ++ D ∧ D.toList.map ArmCertCTOrdered.OrderedEventV2.record = [] := by
  intro final enc0 f
  obtain ⟨acc, nx, hregs⟩ := f.regs
  have sysF : SysEq2 x.regs final.regs := EntryBranchPins.sysEq2_symm _ _ f.input.sys
  have controlsF := HeapV2StepCerts.BlStepV3.caller_controls_fetched x final hregs sysF controls
  obtain ⟨fin, run, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ev, _⟩ :=
    RtB6.RichZ.bl_tailE real imm26 x low final enc0 budget f.pins f.input f.guard f.quiet f.it f.ss controlsF
  exact ⟨fin, run, silent ev⟩
end

#print axioms entry_genE
#print axioms evShape_of_fetchRunD
#print axioms shim_ev
#print axioms tail_btiC
#print axioms tail_classE
#print axioms tail_mrs9
#print axioms tail_msr9
#print axioms tail_ditOn
#print axioms tail_isb
#print axioms tail_ret
#print axioms tail_bl
end RtDit.ShimEv
