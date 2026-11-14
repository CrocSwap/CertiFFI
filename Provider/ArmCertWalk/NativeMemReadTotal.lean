-- Actual AArch64_MemSingle_read4 (IFETCH-shaped access) from current data.
-- Translation: native_translate_address_total at the actual framed prefix state.
-- Bytes: actual Some at the mapped PA in INITIAL memory; availability (not value)
-- after the walk's own descriptor stores via canonical StoreHistory.some_after.
import ArmCertWalk.NativeTranslateAddressTotal
import ArmCertWalk.MemReadPost
import ArmCertTranslateModel.StoreDomain
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk

/-- Four present bytes form the little-endian word read by `PreSail.readBytes 4`. -/
theorem word_of_present_bytes (memory : Mem) (address : Nat)
    (present : ∀ i < 4, ∃ b : BitVec 8, memory[address + i]? = some b) :
    ∃ data : BitVec 32, ∀ i < 4, memory[address + i]? = some (data.extractLsb' (8 * i) 8) := by
  obtain ⟨b0, h0⟩ := present 0 (by decide)
  obtain ⟨b1, h1⟩ := present 1 (by decide)
  obtain ⟨b2, h2⟩ := present 2 (by decide)
  obtain ⟨b3, h3⟩ := present 3 (by decide)
  have l0 := b0.isLt
  have l1 := b1.isLt
  have l2 := b2.isLt
  have l3 := b3.isLt
  refine ⟨BitVec.ofNat 32 (b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat), ?_⟩
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · rw [h0]; congr 1; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]; omega
  · rw [h1]; congr 1; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]; omega
  · rw [h2]; congr 1; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]; omega
  · rw [h3]; congr 1; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]; omega

/-- Mapped code PA is outside the model's GIC/UART special pages (current data
on the mapping, not a new environment premise). -/
def MappedNotMMIO (mapping : BitVec 64 → Option Nat) (va : BitVec 64) : Prop :=
  ∀ pa : BitVec 56, mapping va = some pa.toNat → MemM1.MemReadIF.NotMMIO pa

/-- Actual four Some bytes at the mapped PA in the CURRENT initial memory. -/
def MappedBytesPresent (mapping : BitVec 64 → Option Nat) (va : BitVec 64) (memory : Mem) : Prop :=
  ∀ pa : Nat, mapping va = some pa → ∀ i < 4, ∃ b : BitVec 8, memory[pa + i]? = some b

/-- COMPLETE actual `AArch64_MemSingle_read va 4 acc true` for an IFETCH-shaped
access: real seeds 1631/1632/1633, LSE2/alignment asserts for both LSE2 values,
MTE2/TME queries, actual TranslateAddress (incl. walk AF/dirty stores), SPE,
actual PhysMemRead of the CURRENT post-walk word. The returned word is the
actual post-translation memory content; no pre-walk memory equality. -/
theorem native_mem_read_total {domain : QueryDomain} (spec : TopologyImageSpec domain)
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
      final.regs = translated.regs ∧ final.mem = translated.mem := by
  obtain ⟨address, translated, data, final, ⟨faultOut, clean, bytes⟩, readCall, events, regs, mem⟩ :=
    mem_single_read_post query.va pcAligned query.request.raw initial accShape
      (fun address translated data => ∃ faultOut,
        CleanTranslateResultFields spec config rows mapping query leafLevel view initial
          (faultOut, address) translated ∧
        ∀ i < 4, translated.mem[address.paddress.address.toNat + i]? =
          some (data.extractLsb' (8 * i) 8))
      (by
        intro framed frame
        have frameRegs : framed.regs = initial.regs := frame.1
        have frameMem : framed.mem = initial.mem := frame.2.1
        obtain ⟨address, faultOut, translated, translateCall, completed⟩ :=
          native_translate_address_total spec config rows mapping query member true ((4 : Nat) : Int)
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
          mmio _ mapResult, dataBytes, faultOut, clean, dataBytes⟩)
  exact ⟨address, faultOut, translated, data, final, clean, bytes, readCall, events, regs, mem⟩

#print axioms native_mem_read_total
end ArmCertWalk
