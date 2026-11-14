-- native_mem_read_total plus the SAME call's ordered actual translation traffic
-- (native_translate_address_events_total), for Core's per-step witness.
import ArmCertWalk.NativeMemReadTotal
import ArmCertWalk.NativeTranslateAddressEvents
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk

/-- COMPLETE actual `AArch64_MemSingle_read va 4 acc true` for an IFETCH-shaped
access: real seeds 1631/1632/1633, LSE2/alignment asserts for both LSE2 values,
MTE2/TME queries, actual TranslateAddress (incl. walk AF/dirty stores), SPE,
actual PhysMemRead of the CURRENT post-walk word. The returned word is the
actual post-translation memory content; no pre-walk memory equality. -/
theorem native_mem_read_events_total {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (query : AccessQuery) (member : domain query)
    (leafLevel logical : Nat) (physical : FullAddress) (view : S1DescriptorPIE.View 64)
    (path : S1LogicalReference.Path (logicalObserve spec.logicalRows)
      (effectiveBits spec.physicalConfig).toNat query.va spec.layout.start
      (S1LogicalReference.rootBits spec.layout.start spec.layout.inputBits) spec.layout.root
      (.leaf leafLevel logical physical view))
    (binding : PathPermissionUse spec config rows query path ⟨0#2, false, false⟩)
    (initial : State)
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
          (∀ step ∈ walk, step.2.1 = false) ∧ leaf.2.1 = false ∧ translated.mem = initial.mem) := by
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
            (∀ step ∈ walk, step.2.1 = false) ∧ leaf.2.1 = false ∧ translated.mem = initial.mem))
      (by
        intro framed frame
        have frameRegs : framed.regs = initial.regs := frame.1
        have frameMem : framed.mem = initial.mem := frame.2.1
        have frameEvents : framed.events = initial.events := frame.2.2
        obtain ⟨address, faultOut, translated, translateCall, completed, info, walk, leaf, middle, walkLen,
            trafficOK, endEvents, noUpdate, _⟩ :=
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
            exact result⟩)
  exact ⟨address, faultOut, translated, data, final, clean, bytes, readCall, events, regs, mem, traffic⟩

#print axioms native_mem_read_events_total
end ArmCertWalk
