-- Memory ((F),): fetch_timing_pair. The actual fetch's appended events are, as V2 traffic
-- records, a pure function of (spec, PC, mapping PC): the no-update translation traffic (NoUpdateRecords.trafficRecsOf)
-- then the ifetch read. Two states with equal PC therefore append record-equal events; with equal code bytes they
-- fetch the same word. mem_read_events_slots / fetch_events_slots = native_mem_read_events_total /
-- native_fetch_current_preserving_events also exporting the walk's static slots (dropped there).
import ArmCertWalk.NativeFetchPreservingEvents
import ArmCertWalk.NoUpdateRecords
import ArmCertWalk.FetchRecords
import ArmCertWalk.DataNoUpdate
import HeapV2StepCerts.RawFetch
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace HeapV2StepCerts.FetchTiming
open ArmCertWalk

theorem mem_read_events_slots {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (query : AccessQuery) (member : domain query)
    (leafLevel logical : Nat) (physical : FullAddress) (view : S1DescriptorPIE.View 64)
    (path : S1LogicalReference.Path (logicalObserve spec.logicalRows)
      (effectiveBits spec.physicalConfig).toNat query.va spec.layout.start
      (S1LogicalReference.rootBits spec.layout.start spec.layout.inputBits) spec.layout.root
      (.leaf leafLevel logical physical view))
    (binding : PathPermissionUse spec config rows query path ⟨0#2, false, false⟩)
    (initial : ArmCertWalk.State)
    (lower : AArch64_GetVARange query.va = .VARange_LOWER)
    (current : HostWalkAt config spec.controls spec.physicalConfig initial)
    (mode : HostEL0ModeAt initial.regs)
    (aa64 : initial.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt initial.regs)
    (spe : initial.regs.bank_Bool .SPESampleInFlight = false)
    (bound : HostImageParamsAt initial.regs
      {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (initial.regs.bank_BitVec_64 .TCR_EL2)})
    (geometry : spec.params.txsz = normalizeTxsz initial.regs
      (_get_TCR_EL2_Type_T0SZ (initial.regs.bank_BitVec_64 .TCR_EL2)))
    (layout : CurrentLayoutAt spec.layout spec.params query.va initial.regs)
    (images : CurrentImagesAt spec config rows initial)
    (guard : HostTranslateGuardAt initial.regs spec.params)
    (checked : TranslateQueryChecks initial.regs spec.params query.va query.request.raw)
    (rawFault : sourceTxszFault initial.regs
      {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (initial.regs.bank_BitVec_64 .TCR_EL2)} = false)
    (enabled : currentTranslationEnabled initial.regs = true)
    (accessEL : query.request.raw.el = EL0) (ss : query.request.raw.ss = .SS_NonSecure)
    (cache : initial.regs.bank_Bool .__tlb_enabled = false)
    (epd : currentWalkEPD initial.regs query.va = 0#1)
    (map : LeafMapAt mapping spec.physicalConfig initial.regs query leafLevel view)
    (outputPolicy : OutputCacheAdmissible query.request.raw initial.regs)
    (accShape : MemM1.MemReadIF.AccIFR query.request.raw)
    (pcAligned : query.va.toNat % 4 = 0)
    (mmio : MappedNotMMIO mapping query.va)
    (present : MappedBytesPresent mapping query.va initial.mem) :
    ∃ address faultOut translated data final,
      CleanTranslateResultFields spec config rows mapping query leafLevel view initial
        (faultOut, address) translated ∧
      (∀ i < 4, translated.mem[address.paddress.address.toNat + i]? =
        some (data.extractLsb' (8 * i) 8)) ∧
      AArch64_MemSingle_read query.va 4 query.request.raw true initial = .ok data final ∧
      final.events = translated.events.push
        (.memRead address.paddress.address.toNat 4 (some query.va.toNat) (AK_ifetch ()) false) ∧
      final.regs = translated.regs ∧ final.mem = translated.mem ∧
      ∃ (info : TranslationStartInfo) (walk : List (Nat × Bool × Array Event))
        (leaf : Nat × Bool × Array Event) (middle : Array Event),
        walk.length = leafLevel + 1 - spec.layout.start ∧
        TranslateTrafficFrom (initial.events.push (.translationStart info)) walk leaf middle ∧
        translated.events = middle.push (.translationEnd address) ∧
        (RawImageAt spec.imageRows initial.mem →
          NoUpdateRows {spec.params with haft := hostHAFT initial.regs} query.request.raw spec.imageRows = true →
          (∀ step ∈ walk, step.2.1 = false) ∧ leaf.2.1 = false ∧ translated.mem = initial.mem) ∧
        ((spec.logicalRows.map (·.logical)).Nodup → walk.map (·.1) = declaredSlots spec.logicalRows spec.layout query.va) := by
  obtain ⟨address, translated, data, final, ⟨faultOut, clean, bytes, traffic⟩, readCall, events, regs, mem⟩ :=
    mem_single_read_post query.va pcAligned query.request.raw initial accShape
      (fun address translated data => ∃ faultOut,
        CleanTranslateResultFields spec config rows mapping query leafLevel view initial
          (faultOut, address) translated ∧
        (∀ i < 4, translated.mem[address.paddress.address.toNat + i]? =
          some (data.extractLsb' (8 * i) 8)) ∧
        ∃ (info : TranslationStartInfo) (walk : List (Nat × Bool × Array Event))
          (leaf : Nat × Bool × Array Event) (middle : Array Event),
          walk.length = leafLevel + 1 - spec.layout.start ∧
          TranslateTrafficFrom (initial.events.push (.translationStart info)) walk leaf middle ∧
          translated.events = middle.push (.translationEnd address) ∧
          (RawImageAt spec.imageRows initial.mem →
            NoUpdateRows {spec.params with haft := hostHAFT initial.regs} query.request.raw spec.imageRows = true →
            (∀ step ∈ walk, step.2.1 = false) ∧ leaf.2.1 = false ∧ translated.mem = initial.mem) ∧
        ((spec.logicalRows.map (·.logical)).Nodup → walk.map (·.1) = declaredSlots spec.logicalRows spec.layout query.va))
      (by
        intro framed frame
        have frameRegs : framed.regs = initial.regs := frame.1
        have frameMem : framed.mem = initial.mem := frame.2.1
        have frameEvents : framed.events = initial.events := frame.2.2
        obtain ⟨address, faultOut, translated, translateCall, completed, info, walk, leaf, middle, walkLen,
            trafficOK, endEvents, noUpdate, _, _, slots⟩ :=
          native_translate_address_events_total spec config rows mapping query member true ((4 : Nat) : Int)
            leafLevel logical physical view path binding framed lower
            (host_walk_frame config spec.controls spec.physicalConfig initial framed current frameRegs)
            (by simpa only [frameRegs] using mode) (by rw [frameRegs]; exact aa64)
            (by rw [frameRegs]; exact debug) (by rw [frameRegs]; exact spe)
            (by simpa only [frameRegs] using bound) (by simpa only [frameRegs] using geometry)
            (layout.of_regs frameRegs) (images.frame frameRegs frameMem)
            (by simpa only [frameRegs] using guard) (by simpa only [frameRegs] using checked)
            (by simpa only [frameRegs] using rawFault) (by simpa only [frameRegs] using enabled)
            accessEL ss (by rw [frameRegs]; exact cache) (by rw [frameRegs]; exact epd)
            (by rw [frameRegs]; exact map) (by rw [frameRegs]; exact outputPolicy)
        have clean := clean_translate_result_memory_frames spec config rows mapping query leafLevel view
          initial framed translated translated (faultOut, address) frameRegs frameMem rfl rfl completed
        have kept := clean
        obtain ⟨params, out, operations, active, format, resultFault, faultNone, mapResult, va,
          normal, addressFault, nonsecure, addressPA, registers, history, imagesAfter, held⟩ := kept
        have afterBytes : ∀ i < 4, ∃ b : BitVec 8,
            translated.mem[address.paddress.address.toNat + i]? = some b := by
          intro i hi
          obtain ⟨b, hb⟩ := present _ mapResult i hi
          exact history.some_after _ b hb
        obtain ⟨data, dataBytes⟩ :=
          word_of_present_bytes translated.mem address.paddress.address.toNat afterBytes
        have afterSPE : translated.regs.bank_Bool .SPESampleInFlight = false := by
          rw [registers]
          unfold fetchGuardRegs
          split <;> exact spe
        exact ⟨address, translated, data, translateCall, addressFault, va, afterSPE,
          mmio _ mapResult, dataBytes, faultOut, clean, dataBytes, info, walk, leaf, middle, walkLen,
          by rw [← frameEvents]; exact trafficOK, endEvents, fun raw none => by
            have result := noUpdate (by rw [frameMem]; exact raw) (by rw [frameRegs]; exact none)
            rw [frameMem] at result
            exact result, slots⟩)
  exact ⟨address, faultOut, translated, data, final, clean, bytes, readCall, events, regs, mem, traffic⟩

#print axioms mem_read_events_slots

open ArmCert.Eval.M1a.Fetch2

theorem fetch_events_slots {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s : ArmCertWalk.State) (step : StepFacts s.regs) (el : s.regs.PSTATE.EL = 0#2)
    (pcLow : Sail.BitVec.extractLsb s.regs._PC 1 0 = 0#2) (il : s.regs.PSTATE.IL = 0#1)
    (current : CurrentS1At spec config rows s)
    (mode : HostEL0ModeAt s.regs) (aa64 : s.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt s.regs) (spe : s.regs.bank_Bool .SPESampleInFlight = false)
    (queryOf : AccessDescriptor → AccessQuery)
    (rawOf : ∀ acc, (queryOf acc).request.raw = acc)
    (vaOf : ∀ acc, (queryOf acc).va = s.regs._PC)
    (mmio : MappedNotMMIO mapping s.regs._PC)
    (present : MappedBytesPresent mapping s.regs._PC s.mem)
    (perAcc : ∀ acc, ActualIFetchAcc s acc → domain (queryOf acc) ∧
      ∃ data : S1AccessData spec config rows (queryOf acc),
        CurrentS1AccessAt spec config rows mapping (queryOf acc) data s) :
    ∃ acc word final address faultOut translated,
      ∃ data : S1AccessData spec config rows (queryOf acc),
      ActualIFetchAcc s acc ∧
      __FetchInstr s.regs._PC s = .ok (__InstrEnc.__A64, word) final ∧
      CleanTranslateResultFields spec config rows mapping (queryOf acc) data.leafLevel data.view
        (fetchPre s) (faultOut, address) translated ∧
      (∀ i < 4, translated.mem[address.paddress.address.toNat + i]? =
        some (word.extractLsb' (8 * i) 8)) ∧
      final.regs = translated.regs ∧ final.mem = translated.mem ∧
      final.events = translated.events.push
        (.memRead address.paddress.address.toNat 4 (some s.regs._PC.toNat) (AK_ifetch ()) false) ∧
      CurrentS1At spec config rows final ∧
      CurrentS1AccessAt spec config rows mapping (queryOf acc) data final ∧
      ∃ (info : TranslationStartInfo) (walk : List (Nat × Bool × Array Event))
        (leaf : Nat × Bool × Array Event) (middle : Array Event),
        walk.length = data.leafLevel + 1 - spec.layout.start ∧
        TranslateTrafficFrom ((fetchPre s).events.push (.translationStart info)) walk leaf middle ∧
        translated.events = middle.push (.translationEnd address) ∧
        (RawImageAt spec.imageRows (fetchPre s).mem →
          NoUpdateRows {spec.params with haft := hostHAFT (fetchPre s).regs} (queryOf acc).request.raw
            spec.imageRows = true →
          (∀ step ∈ walk, step.2.1 = false) ∧ leaf.2.1 = false ∧ translated.mem = (fetchPre s).mem) ∧
          ((spec.logicalRows.map (·.logical)).Nodup → walk.map (·.1) = declaredSlots spec.logicalRows spec.layout s.regs._PC) := by
  have pre := current_s1_fetchPre current
  have modePre : HostEL0ModeAt (fetchPre s).regs := host_el0_mode_register_fields mode rfl rfl rfl rfl
  have debugPre : ExistingE11DebugAt (fetchPre s).regs := existing_e11_debug_register_fields debug rfl rfl
  have spePre : (fetchPre s).regs.bank_Bool .SPESampleInFlight = false :=
    (fetchRegs_bool_ne s.regs _ (by decide)).trans spe
  obtain ⟨acc, t, word, u, final, fetchCall, actual, tRegs, tMem, tEvents,
      ⟨address, faultOut, translated, data, clean, bytes, uEvents, uRegs, uMem, postCurrent, postAccess, traffic⟩,
      fRegs, fMem, fEvents⟩ :=
    fetch_frame_post s step pcLow il
      (fun acc t word u => ∃ address faultOut translated,
          ∃ data : S1AccessData spec config rows (queryOf acc),
        CleanTranslateResultFields spec config rows mapping (queryOf acc) data.leafLevel data.view
          (fetchPre s) (faultOut, address) translated ∧
        (∀ i < 4, translated.mem[address.paddress.address.toNat + i]? =
          some (word.extractLsb' (8 * i) 8)) ∧
        u.events = translated.events.push
          (.memRead address.paddress.address.toNat 4 (some s.regs._PC.toNat) (AK_ifetch ()) false) ∧
        u.regs = translated.regs ∧ u.mem = translated.mem ∧
        CurrentS1At spec config rows translated ∧
        CurrentS1AccessAt spec config rows mapping (queryOf acc) data translated ∧
        ∃ (info : TranslationStartInfo) (walk : List (Nat × Bool × Array Event))
          (leaf : Nat × Bool × Array Event) (middle : Array Event),
          walk.length = data.leafLevel + 1 - spec.layout.start ∧
          TranslateTrafficFrom ((fetchPre s).events.push (.translationStart info)) walk leaf middle ∧
          translated.events = middle.push (.translationEnd address) ∧
          (RawImageAt spec.imageRows (fetchPre s).mem →
            NoUpdateRows {spec.params with haft := hostHAFT (fetchPre s).regs} (queryOf acc).request.raw
              spec.imageRows = true →
            (∀ step ∈ walk, step.2.1 = false) ∧ leaf.2.1 = false ∧ translated.mem = (fetchPre s).mem) ∧
          ((spec.logicalRows.map (·.logical)).Nodup → walk.map (·.1) = declaredSlots spec.logicalRows spec.layout s.regs._PC))
      (by
        intro t tRegs _ _
        obtain ⟨acc, after, call, _, frame⟩ :=
          MemM1.MemReadIF.createR t (by rw [tRegs]; exact step.rme) (by rw [tRegs]; exact step.nrw)
            (by rw [tRegs]; exact step.b3) (by rw [tRegs]; exact step.a3) (by rw [tRegs]; exact el)
            (by rw [tRegs]; exact step.ns)
        exact ⟨acc, after, call, frame⟩)
      (by
        intro acc actual t tRegs tMem tEvents
        obtain ⟨t0, u0, t0Regs, t0Call⟩ := actual
        obtain ⟨acc0, after0, call0, shape0, _⟩ :=
          MemM1.MemReadIF.createR t0 (by rw [t0Regs]; exact step.rme) (by rw [t0Regs]; exact step.nrw)
            (by rw [t0Regs]; exact step.b3) (by rw [t0Regs]; exact step.a3) (by rw [t0Regs]; exact el)
            (by rw [t0Regs]; exact step.ns)
        have results := call0.symm.trans t0Call
        have same : acc0 = acc := by injection results
        subst same
        obtain ⟨member, data, access⟩ := perAcc acc0 ⟨t0, u0, t0Regs, t0Call⟩
        have va := vaOf acc0
        have raw := rawOf acc0
        have frameRegs : t.regs = (fetchPre s).regs := tRegs
        have frameMem : t.mem = (fetchPre s).mem := tMem
        have currentT := current_s1_frame pre frameRegs frameMem
        have accessP : CurrentS1AccessAt spec config rows mapping (queryOf acc0) data (fetchPre s) :=
          current_s1_access_registers access rfl rfl rfl rfl rfl rfl (fun _ _ => rfl)
        have accessT : CurrentS1AccessAt spec config rows mapping (queryOf acc0) data t :=
          accessP.of_regs frameRegs
        obtain ⟨address, faultOut, translated, word, final, clean, bytes, readCall, events, regs, mem,
            info, walk, leaf, middle, walkLen, trafficOK, endEvents, noUpdate, slots⟩ :=
          mem_read_events_slots spec config rows mapping (queryOf acc0) member data.leafLevel data.logical
            data.physical data.view data.path data.permissions t data.lower currentT.host
            (by rw [frameRegs]; exact modePre) (by rw [frameRegs]; exact aa64)
            (by rw [frameRegs]; exact debugPre) (by rw [frameRegs]; exact spePre)
            currentT.core currentT.geometry accessT.layout currentT.images currentT.guards accessT.checks
            currentT.rawFault currentT.enabled data.accessEL data.nonsecure currentT.cache accessT.epd
            accessT.map accessT.outputPolicy (by rw [raw]; exact shape0)
            (by rw [va]; exact pc_low_aligned _ pcLow) (by rw [va]; exact mmio)
            (by rw [va, tMem]; exact present)
        have post := current_s1_after data currentT accessT (clean_translate_fields_to_clean clean)
        have cleanPre := clean_translate_result_memory_frames spec config rows mapping (queryOf acc0)
          data.leafLevel data.view (fetchPre s) t translated translated (faultOut, address)
          frameRegs frameMem rfl rfl clean
        have kept := clean
        obtain ⟨_, out, _, _, _, _, _, _, _, _, _, _, _, registers, _⟩ := kept
        refine ⟨word, final, ?_, ?_, address, faultOut, translated, data, cleanPre, bytes,
          by rw [events, va], regs, mem, post.1, post.2, info, walk, leaf, middle, walkLen,
          by rw [tEvents] at trafficOK; exact trafficOK, endEvents,
          fun rawImg none => by
            have result := noUpdate (by rw [frameMem]; exact rawImg) (by rw [frameRegs]; exact none)
            rw [frameMem] at result
            exact result, by rw [← va]; exact slots⟩
        · rw [va, raw] at readCall; exact readCall
        · rw [regs, registers]
          unfold fetchGuardRegs
          split <;> rfl)
  have finalRegs : final.regs = translated.regs := fRegs.trans uRegs
  have finalMem : final.mem = translated.mem := fMem.trans uMem
  exact ⟨acc, word, final, address, faultOut, translated, data, actual, fetchCall, clean, bytes,
    finalRegs, finalMem, fEvents.trans uEvents, current_s1_frame postCurrent finalRegs finalMem,
    postAccess.of_regs finalRegs, traffic⟩

#print axioms fetch_events_slots

/-- **The fetch's appended events as V2 traffic records** (no-update route): the deterministic translation
records of the PC, then the ifetch read at the PC's mapped PA. Memory is unchanged; the word is the 4 bytes there. -/
theorem fetch_records {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s : ArmCertWalk.State) (step : StepFacts s.regs) (el : s.regs.PSTATE.EL = 0#2)
    (pcLow : Sail.BitVec.extractLsb s.regs._PC 1 0 = 0#2) (il : s.regs.PSTATE.IL = 0#1)
    (current : CurrentS1At spec config rows s)
    (mode : HostEL0ModeAt s.regs) (aa64 : s.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt s.regs) (spe : s.regs.bank_Bool .SPESampleInFlight = false)
    (queryOf : AccessDescriptor → AccessQuery)
    (rawOf : ∀ acc, (queryOf acc).request.raw = acc)
    (vaOf : ∀ acc, (queryOf acc).va = s.regs._PC)
    (mmio : MappedNotMMIO mapping s.regs._PC)
    (present : MappedBytesPresent mapping s.regs._PC s.mem)
    (perAcc : ∀ acc, ActualIFetchAcc s acc → domain (queryOf acc) ∧
      ∃ data : S1AccessData spec config rows (queryOf acc),
        CurrentS1AccessAt spec config rows mapping (queryOf acc) data s)
    (raw : RawImageAt spec.imageRows s.mem)
    (noUpd : ∀ (wr : Bool) (acc : AccessDescriptor), DataShape wr acc →
      NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∃ (acc : AccessDescriptor) (word : BitVec 32) (final : ArmCertWalk.State) (n : Nat) (T : Array Event)
      (address : AddressDescriptor) (faultOut : FaultRecord) (translated : ArmCertWalk.State)
      (data : S1AccessData spec config rows (queryOf acc)),
      ActualIFetchAcc s acc ∧
      __FetchInstr s.regs._PC s = .ok (__InstrEnc.__A64, word) final ∧
      mapping s.regs._PC = some n ∧
      final.events = s.events ++ T ++ #[.memRead n 4 (some s.regs._PC.toNat) (AK_ifetch ()) false] ∧
      T.toList.map ArmCertCT.Native.V2.trafficRec = trafficRecsOf spec s.regs._PC ∧
      final.mem = s.mem ∧ (∀ i < 4, s.mem[n + i]? = some (word.extractLsb' (8 * i) 8)) ∧
      CleanTranslateResultFields spec config rows mapping (queryOf acc) data.leafLevel data.view
        (fetchPre s) (faultOut, address) translated ∧ final.regs = translated.regs ∧
      CurrentS1At spec config rows final := by
  obtain ⟨acc, word, final, address, faultOut, translated, data, actual, call, clean, bytes, fregs, fmem, fev,
      curFinal, _, info, walk, leaf, middle, _, traffic, endEv, cond⟩ :=
    fetch_events_slots spec config rows mapping s step el pcLow il current mode aa64 debug spe queryOf rawOf vaOf
      mmio present perAcc
  obtain ⟨condF, slots⟩ := cond
  obtain ⟨flags, leafF, tmem⟩ := condF raw (by
    rw [rawOf acc]
    exact HeapV2StepCerts.RawFetch.noUpd_read noUpd acc (actual_ifetch_flags actual).2.2.1)
  have kept := clean
  obtain ⟨_, _, _, _, _, _, _, mapResult, _, _, _, _, _, _, _, _, _⟩ := kept
  rw [vaOf acc] at mapResult
  obtain ⟨T, hT, recs⟩ := noupdate_traffic_delta (spec := spec) (va := s.regs._PC) (before := (fetchPre s).events)
    (after := translated.events) (ad := address) ⟨info, walk, leaf, middle, traffic, flags, leafF, slots, endEv⟩ nodup
  refine ⟨acc, word, final, address.paddress.address.toNat, T, address, faultOut, translated, data, actual, call,
    mapResult, ?_, recs, fmem.trans tmem, fun i hi => by have b := bytes i hi; rw [tmem] at b; exact b, clean, fregs, curFinal⟩
  rw [fev, hT, Array.push_eq_append]
  rfl

/-- **fetch_timing_pair** ((F)): two states with equal PC (each under the fetch hypotheses and the
no-update facts ChainInv3 carries) append record-equal events, fetch from the same PA, keep memory, and, with equal
bytes at that PA, fetch the same word. -/
theorem fetch_timing_pair {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) {l r : ArmCertWalk.State}
    {wl wr : BitVec 32} {fl fr : ArmCertWalk.State} {nl nr : Nat} {Tl Tr : Array Event}
    (pc : l.regs._PC = r.regs._PC)
    (hl : __FetchInstr l.regs._PC l = .ok (__InstrEnc.__A64, wl) fl ∧ mapping l.regs._PC = some nl ∧
      fl.events = l.events ++ Tl ++ #[.memRead nl 4 (some l.regs._PC.toNat) (AK_ifetch ()) false] ∧
      Tl.toList.map ArmCertCT.Native.V2.trafficRec = trafficRecsOf spec l.regs._PC ∧
      fl.mem = l.mem ∧ (∀ i < 4, l.mem[nl + i]? = some (wl.extractLsb' (8 * i) 8)))
    (hr : __FetchInstr r.regs._PC r = .ok (__InstrEnc.__A64, wr) fr ∧ mapping r.regs._PC = some nr ∧
      fr.events = r.events ++ Tr ++ #[.memRead nr 4 (some r.regs._PC.toNat) (AK_ifetch ()) false] ∧
      Tr.toList.map ArmCertCT.Native.V2.trafficRec = trafficRecsOf spec r.regs._PC ∧
      fr.mem = r.mem ∧ (∀ i < 4, r.mem[nr + i]? = some (wr.extractLsb' (8 * i) 8)))
    (code : ∀ i < 4, l.mem[nl + i]? = r.mem[nl + i]?) :
    nl = nr ∧
    (Tl.toList ++ [Event.memRead nl 4 (some l.regs._PC.toNat) (AK_ifetch ()) false]).map ArmCertCT.Native.V2.trafficRec =
      (Tr.toList ++ [Event.memRead nr 4 (some r.regs._PC.toNat) (AK_ifetch ()) false]).map ArmCertCT.Native.V2.trafficRec ∧
    wl = wr := by
  obtain ⟨_, ml, _, rl, _, bl⟩ := hl
  obtain ⟨_, mr, _, rr, _, br⟩ := hr
  rw [pc] at ml rl
  have hn : nl = nr := Option.some.inj (ml.symm.trans mr)
  subst hn
  refine ⟨rfl, ?_, ?_⟩
  · simp only [List.map_append, rl, rr, List.map_cons, List.map_nil, ifetch_read_record]
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have hi : j / 8 < 4 := by omega
    have e : some (wl.extractLsb' (8 * (j / 8)) 8) = some (wr.extractLsb' (8 * (j / 8)) 8) := by
      rw [← bl _ hi, code _ hi, br _ hi]
    have e' := congrArg (fun v => v.getLsbD (j % 8)) (Option.some.inj e)
    simp only [BitVec.getLsbD_extractLsb'] at e'
    have hm : j % 8 < 8 := Nat.mod_lt _ (by omega)
    have hj' : 8 * (j / 8) + j % 8 = j := by omega
    simpa [hm, hj'] using e'

#print axioms fetch_records
#print axioms fetch_timing_pair
end HeapV2StepCerts.FetchTiming
