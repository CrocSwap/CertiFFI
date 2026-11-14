import Bridge.CruxGenGuarded.EntryBtiNext
import Bridge.CruxGenGuarded.EntryDitOnTail
import Bridge.CruxGenGuarded.EntryDitOffTail
import Bridge.CruxGenGuarded.EntryMrsDitTail
import Bridge.CruxGenGuarded.EntryMsrDitTail
import Bridge.CruxGenGuarded.EntryIsbSyTail
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
namespace ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! Class-generic chain step for every post-entry instruction: the whole
actual model step from a state carrying StepPins and the next-fetch inputs is
actual fetch + the class tail, ending in a state that again carries all of
them. `ClassTail` is exactly what the chain consumes from a fixed class
`native_tail`; each existing class tail is adapted below, nothing re-proved. -/

def ClassTail (real : Type) [Sail.SailReal real] (w : BitVec 32) (writes : NativeEntry.Effects.Writes)
    (K : Int) (source : NativeState) : Prop :=
  ∀ (fetched : NativeState) (enc0 : __InstrEnc) (budget : Nat),
    StepPins fetched → NativeEntryInput.Input source fetched → MetadataGuard fetched →
    HookQuiet (budget + 1) fetched → fetched.regs.ShouldAdvanceIT = false →
    fetched.regs.ShouldAdvanceSS = true →
    ∃ sp a fin, (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      nativeTail real source w enc0 fetched = .ok () fin ∧
      NativeEntryContract.Frame writes (actionState w sp K) a ∧
      HookQuiet budget fin ∧ StepPins fin ∧ SysEq2 a.regs fin.regs ∧
      fin.mem = fetched.mem ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = a.regs.bank_Option_InterruptID .__GIC_Pending ∧
      fin.regs._PC = source.regs._PC + 4#64 ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs

def ClassTailAt (real : Type) [Sail.SailReal real] (w : BitVec 32) (writes : NativeEntry.Effects.Writes)
    (K : Int) (source : NativeState) (next : BitVec 64) : Prop :=
  ∀ (fetched : NativeState) (enc0 : __InstrEnc) (budget : Nat),
    StepPins fetched → NativeEntryInput.Input source fetched → MetadataGuard fetched →
    HookQuiet (budget + 1) fetched → fetched.regs.ShouldAdvanceIT = false →
    fetched.regs.ShouldAdvanceSS = true →
    ∃ sp a fin, (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      nativeTail real source w enc0 fetched = .ok () fin ∧
      NativeEntryContract.Frame writes (actionState w sp K) a ∧
      HookQuiet budget fin ∧ StepPins fin ∧ SysEq2 a.regs fin.regs ∧
      fin.mem = fetched.mem ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = a.regs.bank_Option_InterruptID .__GIC_Pending ∧
      fin.regs._PC = next ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs

theorem ClassTail.at {real : Type} [Sail.SailReal real] {w : BitVec 32}
    {writes : NativeEntry.Effects.Writes} {K : Int} {source : NativeState}
    (h : ClassTail real w writes K source) :
    ClassTailAt real w writes K source (source.regs._PC + 4#64) := h

theorem ditOn_tail (real : Type) [Sail.SailReal real] (source : NativeState)
    (profile : NativeEntryAdapters.DitOn.Profile source) :
    ClassTail real (NativeEntryDispatch.DitOn.word) NativeEntryAdapters.DitOn.writes 703 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, _, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryDitOn.native_tail real source fetched enc0 profile pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

theorem ditOff_tail (real : Type) [Sail.SailReal real] (source : NativeState)
    (profile : NativeEntryAdapters.DitOff.Profile source) :
    ClassTail real (NativeEntryDispatch.DitOff.word) NativeEntryAdapters.DitOff.writes 703 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, _, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryDitOff.native_tail real source fetched enc0 profile pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

theorem mrsDit_tail (real : Type) [Sail.SailReal real] (source : NativeState) (Rt : BitVec 5) (rt : Rt.toNat < 31)
    (profile : NativeEntryAdapters.MrsDit.Profile source) :
    ClassTail real (NativeEntryDispatch.MrsDit.word Rt) NativeEntryAdapters.MrsDit.writes 701 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, _, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryMrsDit.native_tail real source fetched enc0 Rt rt profile pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

theorem msrDit_tail (real : Type) [Sail.SailReal real] (source : NativeState) (Rt : BitVec 5) (rt : Rt.toNat < 31)
    (profile : NativeEntryAdapters.MsrDit.Profile source) :
    ClassTail real (NativeEntryDispatch.MsrDit.word Rt) NativeEntryAdapters.MsrDit.writes 702 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, _, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryMsrDit.native_tail real source fetched enc0 Rt rt profile pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

theorem isbSy_tail (real : Type) [Sail.SailReal real] (source : NativeState)
    (profile : NativeEntryAdapters.IsbSy.Profile source) :
    ClassTail real (NativeEntryDispatch.IsbSy.word) NativeEntryAdapters.IsbSy.writes 483 source := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, _, frame, q, p, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryIsbSy.native_tail real source fetched enc0 profile pins input guard budget quiet it ss
  exact ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np⟩

theorem fetched_steppins (acc : AccessDescriptor) (next : TTWState) (s t : NativeState)
    (hp : StepPins s) (hregs : t.regs = FetchedRegs acc next s) : StepPins t := by
  have e := fetched_pins acc next s t (NativeEntryTail.EntryPins.of_scalar s hp) hregs
  have hb : (ArmBridge.CruxGenGuarded.beforeFetchState s).regs.PSTATE.BTYPE = 0#2 := by
    simpa only [ArmBridge.CruxGenGuarded.beforeFetchState] using hp.btype
  have hn : (ArmBridge.CruxGenGuarded.beforeFetchState s).regs.BTypeNext = 0#2 := by
    simpa only [ArmBridge.CruxGenGuarded.beforeFetchState] using hp.btn
  have btype : t.regs.PSTATE.BTYPE = 0#2 := by
    rw [hregs]; unfold FetchedRegs fetchGuardRegs; split
    · exact hb
    · exact hb
  have btn : t.regs.BTypeNext = 0#2 := by
    rw [hregs]; unfold FetchedRegs fetchGuardRegs; split
    · exact hn
    · exact hn
  exact ⟨e.f4, e.rme, e.spe, e.el, e.nrw, e.edecr, e.cti, e.st, e.edesr, e.btt, e.emu, e.e2h, e.tge,
    e.scrns, e.pmbe, e.mdss, e.pmbs, e.da, e.di, e.df, e.il, e.pss, btype, btn⟩

run_cmd do
  IO.eprintln "CURRENT_DECL EntryClassNext.entry_class_next"
  (← IO.getStderr).flush

theorem entry_class_next (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (s : NativeState) (stepPins : StepPins s) (tail : ClassTail real w writes K s)
    (hGIC : s.regs.bank_Option_InterruptID .__GIC_Pending = none)
    (features : EntryFeatures s.regs) (debug : E11Debug.E11CheckDebug s.regs)
    (budget : Nat) (quiet : HookQuiet (budget + 1) s)
    (base offset : BitVec 64) (placed : s.regs._PC = base + offset)
    (page : base.toNat % 4096 = 0) (word : offset.toNat % 4 = 0)
    (current : CurrentS1At spec config rows (ArmBridge.CruxGenGuarded.beforeFetchState s))
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
    ∃ fin,
      modelStep real s = .ok () fin ∧
      StepPins fin ∧ HookQuiet budget fin ∧
      CurrentS1At spec config rows (ArmBridge.CruxGenGuarded.beforeFetchState fin) ∧
      fin.regs._PC = base + (offset + 4#64) ∧
      E11Debug.E11CheckDebug fin.regs ∧ EntryFeatures fin.regs ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = none := by
  have pins := NativeEntryTail.EntryPins.of_scalar s stepPins
  obtain ⟨step, el, il, _pc, emu0, e11, mode, spe⟩ := before_fetch_facts s pins features debug
  obtain ⟨acc, w', final, address, faultOut, translated, data, _actual, run, clean, bytes, fregs,
      _fmem, _fev, curFinal, _⟩ :=
    native_fetch_current_preserving spec config rows mapping (ArmBridge.CruxGenGuarded.beforeFetchState s)
      step el (pc_low_of_placement _ base offset placed page word) il current mode step.b0
      ⟨e11.mde, e11.hde⟩ spe queryOf rawOf vaOf mmio present perAcc
  have hw := code acc data.leafLevel data.view faultOut address translated w' clean bytes
  subst hw
  obtain ⟨_, out, _, _, _, _, _, _, _, _, _, _, _, translatedRegs, _⟩ := clean
  have hregs : final.regs = FetchedRegs acc (translateCurrent out) s := by
    rw [fregs, translatedRegs, rawOf acc]; rfl
  have emuFinal : final.regs.__emulator_termination_opcode = none := by
    rw [hregs]; unfold FetchedRegs fetchGuardRegs; split
    · exact emu0
    · exact emu0
  obtain ⟨enc0, hstep⟩ := entry_prefetch_boundary real s final _ pins hGIC run emuFinal
  have fpins := fetched_steppins acc (translateCurrent out) s final stepPins hregs
  have finput := fetched_input acc (translateCurrent out) s final pins.el hregs
  obtain ⟨guard, fquiet, it, ss⟩ :=
    fetched_rest acc (translateCurrent out) s final (budget + 1) pins quiet hregs
  obtain ⟨sp, a, fin, hook, tail, frame, finQuiet, finStep, sys, mem, gic, pc, np⟩ :=
    tail final enc0 budget fpins finput guard fquiet it ss
  have post := entry_spec_post final sp (budget + 1) fquiet hook
  have finPins := NativeEntryTail.EntryPins.of_scalar fin finStep
  have curFin := ArmBridge.CruxGenGuarded.EntryBtiNext.tail_current _ _ _ final sp a fin curFinal post.frame frame sys np
    (finPins.el.trans fpins.el.symm) (finPins.nrw.trans fpins.nrw.symm) (mem)
  -- register-field chains fin ← a ← action ← sp ← final ← entry
  have toFinal64 : ∀ k : Bank_BitVec_64, (∀ x : Regs, (eraseE20 x).bank_BitVec_64 k = x.bank_BitVec_64 k) →
      a.regs.bank_BitVec_64 k = final.regs.bank_BitVec_64 k := by
    intro k hk
    rw [congrFun frame.b64 k]
    show sp.regs.bank_BitVec_64 k = _
    exact frame_pres_E20 (fun x => x.bank_BitVec_64 k) hk post.frame
  have mdscrFinal : final.regs.bank_BitVec_64 .MDSCR_EL1 = s.regs.bank_BitVec_64 .MDSCR_EL1 := by
    rw [hregs]
    refine ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.bank_BitVec_64 .MDSCR_EL1) _ _ s (fun _ _ => rfl) (fun _ => rfl) ?_
    simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne]
  have mdscr : fin.regs.bank_BitVec_64 .MDSCR_EL1 = s.regs.bank_BitVec_64 .MDSCR_EL1 := by
    rw [sys.mdscr, toFinal64 _ (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]), mdscrFinal]
  have hdeFinal : _get_EDSCR_Type_HDE (final.regs.bank_BitVec_32 ._EDSCR) =
      _get_EDSCR_Type_HDE (s.regs.bank_BitVec_32 ._EDSCR) := by
    rw [hregs]
    refine ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => _get_EDSCR_Type_HDE (r.bank_BitVec_32 ._EDSCR)) _ _ s
      (fun _ _ => rfl) (fun _ => rfl) ?_
    simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne, RegMap.set_same]
    exact ArmBridge.CruxCore.hde_pipeadv _ _
  have hdeA : _get_EDSCR_Type_HDE (a.regs.bank_BitVec_32 ._EDSCR) =
      _get_EDSCR_Type_HDE (final.regs.bank_BitVec_32 ._EDSCR) := by
    rw [congrFun frame.b32 ._EDSCR]
    simp (disch := decide) only [actionState, RegMap.set_ne]
    exact frame_pres_E20 (fun x => _get_EDSCR_Type_HDE (x.bank_BitVec_32 ._EDSCR)) (fun x => by
      simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame
  have featFin : fin.regs.FeatureImpl = s.regs.FeatureImpl := by
    rw [sys.feat, frame.feat]
    show sp.regs.FeatureImpl = _
    rw [frame_pres_E20 (fun x => x.FeatureImpl) (fun x => by
      simp (disch := decide) only [eraseE20]) post.frame, hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.FeatureImpl) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have gicFin : fin.regs.bank_Option_InterruptID .__GIC_Pending = none := by
    rw [gic, frame.gic]
    show sp.regs.bank_Option_InterruptID .__GIC_Pending = _
    rw [post.gic, hregs]
    rw [ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.bank_Option_InterruptID .__GIC_Pending) _ _ s (fun _ _ => rfl)
      (fun _ => rfl) rfl]
    exact hGIC
  refine ⟨fin, hstep.trans tail, finStep, finQuiet,
    ArmBridge.CruxGenGuarded.EntryBtiNext.before_fetch_current fin curFin, ?_, ⟨?_, ?_⟩, ?_, gicFin⟩
  · rw [pc, placed, BitVec.add_assoc]
  · rw [mdscr]; exact debug.mde
  · rw [sys.hde, hdeA, hdeFinal]; exact debug.hde
  · exact ⟨featFin ▸ features.a0, featFin ▸ features.a1, featFin ▸ features.a2, featFin ▸ features.a3,
      featFin ▸ features.b1, featFin ▸ features.b2, featFin ▸ features.b3, featFin ▸ features.vhe⟩

run_cmd do
  IO.eprintln "CURRENT_DECL EntryClassNext.entry_class_next_at"
  (← IO.getStderr).flush

/-- Branch/call/return form: the class contract fixes the actual successor PC
`next`; the chain carries all next-fetch inputs to `base + nextOffset`. -/
theorem entry_class_next_at (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (s : NativeState) (stepPins : StepPins s) (next nextOffset : BitVec 64)
    (tail : ClassTailAt real w writes K s next)
    (hGIC : s.regs.bank_Option_InterruptID .__GIC_Pending = none)
    (features : EntryFeatures s.regs) (debug : E11Debug.E11CheckDebug s.regs)
    (budget : Nat) (quiet : HookQuiet (budget + 1) s)
    (base offset : BitVec 64) (placed : s.regs._PC = base + offset)
    (page : base.toNat % 4096 = 0) (word : offset.toNat % 4 = 0)
    (nextPlaced : next = base + nextOffset)
    (current : CurrentS1At spec config rows (ArmBridge.CruxGenGuarded.beforeFetchState s))
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
    ∃ fin,
      modelStep real s = .ok () fin ∧
      StepPins fin ∧ HookQuiet budget fin ∧
      CurrentS1At spec config rows (ArmBridge.CruxGenGuarded.beforeFetchState fin) ∧
      fin.regs._PC = base + nextOffset ∧
      E11Debug.E11CheckDebug fin.regs ∧ EntryFeatures fin.regs ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = none := by
  have pins := NativeEntryTail.EntryPins.of_scalar s stepPins
  obtain ⟨step, el, il, _pc, emu0, e11, mode, spe⟩ := before_fetch_facts s pins features debug
  obtain ⟨acc, w', final, address, faultOut, translated, data, _actual, run, clean, bytes, fregs,
      _fmem, _fev, curFinal, _⟩ :=
    native_fetch_current_preserving spec config rows mapping (ArmBridge.CruxGenGuarded.beforeFetchState s)
      step el (pc_low_of_placement _ base offset placed page word) il current mode step.b0
      ⟨e11.mde, e11.hde⟩ spe queryOf rawOf vaOf mmio present perAcc
  have hw := code acc data.leafLevel data.view faultOut address translated w' clean bytes
  subst hw
  obtain ⟨_, out, _, _, _, _, _, _, _, _, _, _, _, translatedRegs, _⟩ := clean
  have hregs : final.regs = FetchedRegs acc (translateCurrent out) s := by
    rw [fregs, translatedRegs, rawOf acc]; rfl
  have emuFinal : final.regs.__emulator_termination_opcode = none := by
    rw [hregs]; unfold FetchedRegs fetchGuardRegs; split
    · exact emu0
    · exact emu0
  obtain ⟨enc0, hstep⟩ := entry_prefetch_boundary real s final _ pins hGIC run emuFinal
  have fpins := fetched_steppins acc (translateCurrent out) s final stepPins hregs
  have finput := fetched_input acc (translateCurrent out) s final pins.el hregs
  obtain ⟨guard, fquiet, it, ss⟩ :=
    fetched_rest acc (translateCurrent out) s final (budget + 1) pins quiet hregs
  obtain ⟨sp, a, fin, hook, tail, frame, finQuiet, finStep, sys, mem, gic, pc, np⟩ :=
    tail final enc0 budget fpins finput guard fquiet it ss
  have post := entry_spec_post final sp (budget + 1) fquiet hook
  have finPins := NativeEntryTail.EntryPins.of_scalar fin finStep
  have curFin := ArmBridge.CruxGenGuarded.EntryBtiNext.tail_current _ _ _ final sp a fin curFinal post.frame frame sys np
    (finPins.el.trans fpins.el.symm) (finPins.nrw.trans fpins.nrw.symm) (mem)
  -- register-field chains fin ← a ← action ← sp ← final ← entry
  have toFinal64 : ∀ k : Bank_BitVec_64, (∀ x : Regs, (eraseE20 x).bank_BitVec_64 k = x.bank_BitVec_64 k) →
      a.regs.bank_BitVec_64 k = final.regs.bank_BitVec_64 k := by
    intro k hk
    rw [congrFun frame.b64 k]
    show sp.regs.bank_BitVec_64 k = _
    exact frame_pres_E20 (fun x => x.bank_BitVec_64 k) hk post.frame
  have mdscrFinal : final.regs.bank_BitVec_64 .MDSCR_EL1 = s.regs.bank_BitVec_64 .MDSCR_EL1 := by
    rw [hregs]
    refine ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.bank_BitVec_64 .MDSCR_EL1) _ _ s (fun _ _ => rfl) (fun _ => rfl) ?_
    simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne]
  have mdscr : fin.regs.bank_BitVec_64 .MDSCR_EL1 = s.regs.bank_BitVec_64 .MDSCR_EL1 := by
    rw [sys.mdscr, toFinal64 _ (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]), mdscrFinal]
  have hdeFinal : _get_EDSCR_Type_HDE (final.regs.bank_BitVec_32 ._EDSCR) =
      _get_EDSCR_Type_HDE (s.regs.bank_BitVec_32 ._EDSCR) := by
    rw [hregs]
    refine ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => _get_EDSCR_Type_HDE (r.bank_BitVec_32 ._EDSCR)) _ _ s
      (fun _ _ => rfl) (fun _ => rfl) ?_
    simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne, RegMap.set_same]
    exact ArmBridge.CruxCore.hde_pipeadv _ _
  have hdeA : _get_EDSCR_Type_HDE (a.regs.bank_BitVec_32 ._EDSCR) =
      _get_EDSCR_Type_HDE (final.regs.bank_BitVec_32 ._EDSCR) := by
    rw [congrFun frame.b32 ._EDSCR]
    simp (disch := decide) only [actionState, RegMap.set_ne]
    exact frame_pres_E20 (fun x => _get_EDSCR_Type_HDE (x.bank_BitVec_32 ._EDSCR)) (fun x => by
      simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame
  have featFin : fin.regs.FeatureImpl = s.regs.FeatureImpl := by
    rw [sys.feat, frame.feat]
    show sp.regs.FeatureImpl = _
    rw [frame_pres_E20 (fun x => x.FeatureImpl) (fun x => by
      simp (disch := decide) only [eraseE20]) post.frame, hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.FeatureImpl) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have gicFin : fin.regs.bank_Option_InterruptID .__GIC_Pending = none := by
    rw [gic, frame.gic]
    show sp.regs.bank_Option_InterruptID .__GIC_Pending = _
    rw [post.gic, hregs]
    rw [ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.bank_Option_InterruptID .__GIC_Pending) _ _ s (fun _ _ => rfl)
      (fun _ => rfl) rfl]
    exact hGIC
  refine ⟨fin, hstep.trans tail, finStep, finQuiet,
    ArmBridge.CruxGenGuarded.EntryBtiNext.before_fetch_current fin curFin, ?_, ⟨?_, ?_⟩, ?_, gicFin⟩
  · rw [pc, nextPlaced]
  · rw [mdscr]; exact debug.mde
  · rw [sys.hde, hdeA, hdeFinal]; exact debug.hde
  · exact ⟨featFin ▸ features.a0, featFin ▸ features.a1, featFin ▸ features.a2, featFin ▸ features.a3,
      featFin ▸ features.b1, featFin ▸ features.b2, featFin ▸ features.b3, featFin ▸ features.vhe⟩

#print axioms fetched_steppins
#print axioms entry_class_next_at
#print axioms entry_class_next
#print axioms ditOn_tail
#print axioms ditOff_tail
#print axioms mrsDit_tail
#print axioms msrDit_tail
#print axioms isbSy_tail
end ArmBridge.CruxGenGuarded.EntryClassNext
