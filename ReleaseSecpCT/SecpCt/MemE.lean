-- secp CT0: the event version of Xlate's TranslateSpan.DefaultEntryMem.entry_mem_next_choice (only the
-- EvShape conclusion), by the same transform Memory's mkE14.py applied to EntryMemG -> EntryMemGE.
-- Actual fetched memory continuation with default controls and bounded oracle transport.
import TranslateSpan.DefaultEntryMem
import ArmCertMemPipe.EvD
import HeapV2StepCerts.FetchTiming
import TranslateSpan.DefaultClass
import TagCheckFrames.Fetch
import NativeTagCheck.BeforeFetch
import HeapV2StepCerts.Carry
import HeapV2StepCerts.RegVal
import HeapV2StepCerts.RawFetch
import HeapV2StepCerts.C3Core
import HeapV2StepCerts.MemConfigFrame
import Bridge.CruxGenGuarded.ChainInvV3
import HeapV2StepCerts.DataBytes
import HeapV2StepCerts.FetchFrames
import HeapV2StepCerts.MemNextV3
import HeapV2StepCerts.Flags
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
namespace SecpCt
open TranslateSpan.DefaultEntryMem TranslateSpan
open ArmCertMemPipe NativeAccess ArmBridge.CruxGen NativeMteTagCheck
open HeapV2StepCerts HeapV2StepCerts.MemNext
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
set_option maxHeartbeats 400000

theorem mem_ev (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (s : NativeState) (stepPins : StepPins s) (next nextOffset : BitVec 64)
    (us : List (RegBind.Reg × RegBind.Upd))
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (X : NativeState → Prop) (D : Nat → Prop)
    (Pay : NativeState → NativeState → Prop)
    (catalogue : ControlCatalogue) (cost : Nat)
    (Ctx : NativeState → Prop)
    (adapt : ∀ f, DefaultFetchCtx spec config rows mapping m X catalogue f →
      ChoiceDelta s f 0 → Ctx f)
    (dataOf : NativeState → List (Option ArmCertCTOrdered.OrderedEventV2.Record))
    (xferData : ∀ f : NativeState, f.regs.gpr = s.regs.gpr → f.regs.SP_EL0 = s.regs.SP_EL0 → dataOf f = dataOf s)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (tail : MemTailAt real spec config rows Ctx D w writes K s next us (fun f g => Pay f g ∧ ArmCertMemPipe.EvD spec (dataOf f) f g) cost)
    (hGIC : s.regs.bank_Option_InterruptID .__GIC_Pending = none)
    (features : EntryFeatures s.regs) (debug : E11Debug.E11CheckDebug s.regs)
    (budget : Nat) (quiet : HookQuiet (budget + 1) s)
    (base offset : BitVec 64) (placed : s.regs._PC = base + offset)
    (page : base.toNat % 4096 = 0) (word : offset.toNat % 4 = 0)
    (nextPlaced : next = base + nextOffset)
    (current : CurrentS1At spec config rows (ArmBridge.CruxGenGuarded.beforeFetchState s))
    (closed : ClosedMembershipAt spec config rows mapping m (ArmBridge.CruxGenGuarded.beforeFetchState s))
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (placedImg : MemReloc.ImageOn scope image s loadBase mapping)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (codeD : ImageTableSeparated scope loadBase mapping D)
    (rawS : RawImageAt spec.imageRows s.mem)
    (noUpdS : ∀ (wr : Bool) (acc : AccessDescriptor), DataShape wr acc →
      NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (xferX : ∀ f : NativeState, f.regs.gpr = s.regs.gpr → f.regs.SP_EL0 = s.regs.SP_EL0 → f.mem = s.mem → X f)
    (xferPay : ∀ f g : NativeState, f.regs.gpr = s.regs.gpr → f.regs.SP_EL0 = s.regs.SP_EL0 → f.mem = s.mem →
      Flags.nzcv f.regs = Flags.nzcv s.regs → Pay f g → Pay s g)
    (postS : MemM1.MemReadD.PostRegs s.regs) (modeS : HostEL0ModeAt s.regs)
    (controlsS : DefaultAt catalogue s) (allowedS : TagStatusOK s)
    (edebugS : ExistingE11DebugAt s.regs)
    (featS : s.regs.FeatureImpl[7] = true ∧ s.regs.FeatureImpl[3] = false ∧
      s.regs.FeatureImpl[227] = false ∧ s.regs.FeatureImpl[111] = true)
    (dcacheS : currentDCache s.regs = true)
    (queryOf : AccessDescriptor → AccessQuery)
    (rawOf : ∀ acc, (queryOf acc).request.raw = acc)
    (vaOf : ∀ acc, (queryOf acc).va = s.regs._PC)
    (mmio : MappedNotMMIO mapping s.regs._PC)
    (present : MappedBytesPresent mapping s.regs._PC s.mem)
    (perAcc : ∀ acc, ActualIFetchAcc (ArmBridge.CruxGenGuarded.beforeFetchState s) acc →
      domain (queryOf acc) ∧ ∃ data : S1AccessData spec config rows (queryOf acc),
        CurrentS1AccessAt spec config rows mapping (queryOf acc) data
          (ArmBridge.CruxGenGuarded.beforeFetchState s))
    (code : ∀ acc leafLevel view faultOut (address : AddressDescriptor) translated (word' : BitVec 32),
      CleanTranslateResultFields spec config rows mapping (queryOf acc) leafLevel view
        (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState s)) (faultOut, address) translated →
      (∀ i < 4, translated.mem[address.paddress.address.toNat + i]? = some (word'.extractLsb' (8 * i) 8)) →
      word' = w) :
    ∃ fin, modelStep real s = .ok () fin ∧ ArmBridge.CruxGenGuarded.StepEvents.EvShape spec mapping (dataOf s) s fin := by
  have pins := NativeEntryTail.EntryPins.of_scalar s stepPins
  obtain ⟨step, el, il, _pc, emu0, e11, mode, spe⟩ := before_fetch_facts s pins features debug
  obtain ⟨acc, w', final, address, faultOut, translated, data, actualAcc, run, clean, bytes, fregs,
      fmem, fev, curFinal, _, info, walk, leaf, middle, _len, traffic, endEv, cond⟩ :=
    HeapV2StepCerts.FetchTiming.fetch_events_slots spec config rows mapping (ArmBridge.CruxGenGuarded.beforeFetchState s)
      step el (pc_low_of_placement _ base offset placed page word) il current mode step.b0
      ⟨e11.mde, e11.hde⟩ spe queryOf rawOf vaOf mmio present perAcc
  obtain ⟨noUpdCond, slots⟩ := cond
  obtain ⟨_, _, final', _, _, _, _, _, run', _, _, _, _, _, _, _, fetchChoice, _⟩ :=
    native_fetch_current_preserving_events_choice spec config rows mapping (ArmBridge.CruxGenGuarded.beforeFetchState s)
      step el (pc_low_of_placement _ base offset placed page word) il current mode step.b0
      ⟨e11.mde, e11.hde⟩ spe queryOf rawOf vaOf mmio present perAcc
  have same : final' = final := by
    rw [run] at run'
    injection run' with h1 h2
    exact h2.symm
  subst same
  have fetchedChoice : ChoiceDelta s final' 0 := by
    simpa only [Nat.zero_add] using
      choice_delta_trans (NativeTagCheck.before_fetch_choice s) fetchChoice
  have hw := code acc data.leafLevel data.view faultOut address translated w' clean bytes
  have mapResult : mapping s.regs._PC = some address.paddress.address.toNat := by
    have kept := clean
    obtain ⟨_, _, _, _, _, _, _, mr, _, _, _, _, _, _, _, _, _⟩ := kept
    rw [vaOf acc] at mr; exact mr
  subst hw
  have closedFinal := closed_membership_after_fetch closed clean fregs
  obtain ⟨_, out, _, _, _, _, _, _, _, _, _, _, _, translatedRegs, _⟩ := clean
  have hregs : final'.regs = FetchedRegs acc (translateCurrent out) s := by
    rw [fregs, translatedRegs, rawOf acc]; rfl
  have emuFinal : final'.regs.__emulator_termination_opcode = none := by
    rw [hregs]; unfold FetchedRegs fetchGuardRegs; split
    · exact emu0
    · exact emu0
  obtain ⟨enc0, hstep⟩ := entry_prefetch_boundary real s final' _ pins hGIC run emuFinal
  have fpins := EntryClassNext.fetched_steppins acc (translateCurrent out) s final' stepPins hregs
  have finput := fetched_input acc (translateCurrent out) s final' pins.el hregs
  obtain ⟨guard, fquiet, it, ss⟩ :=
    fetched_rest acc (translateCurrent out) s final' (budget + 1) pins quiet hregs
  have nuC := noUpdCond rawS (by
      rw [rawOf acc]
      exact HeapV2StepCerts.RawFetch.noUpd_read noUpdS acc (actual_ifetch_flags actualAcc).2.2.1)
  have memNoUpd : translated.mem = (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState s)).mem := nuC.2.2
  obtain ⟨flagsT, leafF, _⟩ := nuC
  obtain ⟨T, hT, recsT⟩ := ArmCertWalk.noupdate_traffic_delta ⟨info, walk, leaf, middle, traffic, flagsT, leafF, slots, endEv⟩ nodup
  have pcB : (ArmBridge.CruxGenGuarded.beforeFetchState s).regs._PC = s.regs._PC := rfl
  have evB : (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState s)).events = s.events := rfl
  rw [pcB] at recsT
  have finalMem : final'.mem = s.mem := fmem.trans memNoUpd
  have finalEv : final'.events = s.events ++ T ++ #[ArmBridge.CruxGenGuarded.StepEvents.ifetchEv address.paddress.address.toNat s.regs._PC] := by
    rw [fev, hT, evB, Array.push_eq_append, pcB]; rfl
  have gprFinal : final'.regs.gpr = s.regs.gpr := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.gpr) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have spFinal : final'.regs.SP_EL0 = s.regs.SP_EL0 := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.SP_EL0) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have sysF : SysEq2 s.regs final'.regs := EntryBranchPins.sysEq2_symm _ _ finput.sys
  have tcoFetch : final'.regs.PSTATE.TCO = s.regs.PSTATE.TCO := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.PSTATE.TCO)
      _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have ctx : DefaultFetchCtx spec config rows mapping m X catalogue final' :=
    { closed := closedFinal
      prog := xferX final' gprFinal spFinal finalMem
      raw := by rw [finalMem]; exact rawS
      noUpd := fun wr acc hs => by rw [hostHAFT_eq sysF]; exact noUpdS wr acc hs
      post := CurrentMTE2.post_of_sys sysF postS
      current := curFinal
      controls := DefaultMTE2.controls_of_sys controlsS sysF tcoFetch
      allowed := tag_status_transport fetchedChoice allowedS
      mode := HeapV2StepCerts.MemConfigFrame.mode sysF.feat sysF.el sysF.scr sysF.hcr modeS
      debug := HeapV2StepCerts.MemConfigFrame.debug sysF.mdscr sysF.hde edebugS
      feat := by rw [sysF.feat]; exact featS
      dcache := HeapV2StepCerts.MemConfigFrame.dcache sysF.sctlr dcacheS }
  obtain ⟨sp, a, fin, written, hook, tail, frame, finQuiet, finStep, sys, wo, sepT, inD, gic, pc, np, keep, holdsF, ⟨payF, delta, evD, recsD⟩, traceF⟩ :=
    tail final' enc0 budget fpins finput guard fquiet it ss curFinal (adapt final' ctx fetchedChoice)
  exact ⟨fin, hstep.trans tail, ⟨address.paddress.address.toNat, T, delta, by rw [evD, finalEv], recsT, mapResult,
    by rw [← xferData final' gprFinal spFinal]; exact recsD nodup⟩⟩

end SecpCt
#print axioms SecpCt.mem_ev
