-- (iii): the actual 1-byte data read / n-byte data store from the canonical invariant,
-- now also exposing the ORDERED actual translation traffic preceding the data access event
-- (TranslateEventsAt), so the step delta = translation traffic ++ [access] is Covered.
import ArmCertWalk.NativeDataAccess
import ArmCertWalk.CurrentTranslateEvents
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk

/-- Actual translation traffic from `initial` to `translated` (no-update, WB and slot facts). -/
def TranslateEventsAt {domain : QueryDomain} (spec : TopologyImageSpec domain) (query : AccessQuery)
    (leafLevel : Nat) (initial : State) (address : AddressDescriptor) (translated : State) : Prop :=
  ∃ (info : TranslationStartInfo) (walk : List (Nat × Bool × Array Event))
    (leaf : Nat × Bool × Array Event) (middle : Array Event),
    walk.length = leafLevel + 1 - spec.layout.start ∧
    TranslateTrafficFrom (initial.events.push (.translationStart info)) walk leaf middle ∧
    translated.events = middle.push (.translationEnd address) ∧
    (RawImageAt spec.imageRows initial.mem →
      NoUpdateRows {spec.params with haft := hostHAFT initial.regs} query.request.raw spec.imageRows = true →
      (∀ step ∈ walk, step.2.1 = false) ∧ leaf.2.1 = false ∧ translated.mem = initial.mem) ∧
    (outputCached query.request.raw initial.regs = true →
      address.memattrs.inner.attrs = MemAttr_WB ∧ address.memattrs.outer.attrs = MemAttr_WB) ∧
    ((spec.logicalRows.map (·.logical)).Nodup →
      walk.map (·.1) = declaredSlots spec.logicalRows spec.layout query.va)

theorem native_data_read1_events {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (query : AccessQuery) (member : domain query) (data : S1AccessData spec config rows query)
    (initial : State) (current : CurrentS1At spec config rows initial)
    (access : CurrentS1AccessAt spec config rows mapping query data initial)
    (mode : HostEL0ModeAt initial.regs) (aa64 : initial.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt initial.regs) (post : MemM1.MemReadD.PostRegs initial.regs)
    (shape : MemM1.MemReadD.AccDR query.request.raw)
    (alignedQ : query.request.aligned = true) (sizeQ : query.size = ((1 : Nat) : Int))
    (pa : BitVec 56) (mapped : mapping query.va = some pa.toNat)
    (mmio : MemM1.MemReadIF.NotMMIO pa)
    (value : BitVec (1 * 8)) (byte : initial.mem[pa.toNat]? = some value)
    (outside : ¬ (rowsFootprint spec.imageRows).byte pa.toNat) :
    ∃ address translated final, ∃ faultOut : FaultRecord,
      CleanTranslateResultFields spec config rows mapping query data.leafLevel data.view initial
        (faultOut, address) translated ∧
      CurrentS1At spec config rows translated ∧
      CurrentS1AccessAt spec config rows mapping query data translated ∧
      TranslateEventsAt spec query data.leafLevel initial address translated ∧
      Mem_read query.va 1 query.request.raw initial = .ok value final ∧
      final.events = translated.events.push (.memRead pa.toNat 1 (some address.vaddress.toNat)
        (AccessDescriptor_to_Access_kind query.request.raw) false) ∧
      final.regs = translated.regs ∧ final.mem = translated.mem := by
  obtain ⟨address, translated, final, ⟨faultOut, clean, currentT, accessT, eventsT⟩, call, events, regs, mem⟩ :=
    MemM1.MemReadD.memRead1 query.va (Nat.mod_one _) query.request.raw initial pa value shape
      (fun address translated => ∃ faultOut : FaultRecord,
        CleanTranslateResultFields spec config rows mapping query data.leafLevel data.view initial
          (faultOut, address) translated ∧
        CurrentS1At spec config rows translated ∧
        CurrentS1AccessAt spec config rows mapping query data translated ∧
        TranslateEventsAt spec query data.leafLevel initial address translated)
      (by
        intro framed frame
        have frameRegs : framed.regs = initial.regs := frame.1
        have frameMem : framed.mem = initial.mem := frame.2.1
        obtain ⟨address, faultOut, other, translateCall, fields, currentO, accessO, _, _, _, _, _,
            writes, _, info, walk, leaf, middle, walkLen, traffic, endEv, cond, wb, slots⟩ :=
          current_translate_address_events spec config rows mapping query member data framed
            (current_s1_frame current frameRegs frameMem) (access.of_regs frameRegs)
            (by rw [frameRegs]; exact mode) (by rw [frameRegs]; exact aa64)
            (by rw [frameRegs]; exact debug) (by rw [frameRegs]; exact post.spe)
        rw [alignedQ, sizeQ] at translateCall
        have cleanInitial := clean_translate_result_memory_frames spec config rows mapping query
          data.leafLevel data.view initial framed other other (faultOut, address) frameRegs frameMem
          rfl rfl fields
        have kept := fields
        obtain ⟨_, out, _, _, _, _, _, mapResult, _, _, addressFault, _, _, registers, _⟩ := kept
        have addressPA : address.paddress.address = pa :=
          BitVec.eq_of_toNat_eq (Option.some.inj (mapResult.symm.trans mapped))
        refine ⟨address, other, translateCall, addressFault, addressPA, ?_, ?_,
          faultOut, cleanInitial, currentO, accessO,
          ⟨info, walk, leaf, middle, walkLen, by rw [← frame.2.2]; exact traffic, endEv,
            fun raw none => by
              obtain ⟨f1, f2, f3⟩ := cond (by rw [frameMem]; exact raw) (by rw [frameRegs]; exact none)
              exact ⟨f1, f2, f3.trans frameMem⟩,
            fun cached => wb (by rw [frameRegs]; exact cached), slots⟩⟩
        · rw [registers, frameRegs]
          exact post_regs_data _ _ _ shape.gpr post
        · intro i hi
          obtain rfl : i = 0 := by omega
          have unchanged := writes _ outside
          simp only at unchanged
          simp only [Nat.add_zero, Nat.mul_zero]
          rw [unchanged, frameMem, byte]
          congr 1
          apply BitVec.eq_of_toNat_eq
          simp [BitVec.extractLsb'_toNat])
      mmio
  exact ⟨address, translated, final, faultOut, clean, currentT, accessT, eventsT, call, events, regs, mem⟩

theorem native_data_write_events {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (query : AccessQuery) (member : domain query) (data : S1AccessData spec config rows query)
    (initial : State) (current : CurrentS1At spec config rows initial)
    (access : CurrentS1AccessAt spec config rows mapping query data initial)
    (mode : HostEL0ModeAt initial.regs) (aa64 : initial.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt initial.regs) (spe : initial.regs.bank_Bool .SPESampleInFlight = false)
    (n : Nat) (sizeOK : MemM1.MemWriteD1.SizeOK n)
    (shape : MemM1.MemWriteD5.AccDWT query.request.raw)
    (pre : MemM1.MemWriteD6.PreW query.request.raw initial.regs)
    (alignedQ : query.request.aligned = true) (sizeQ : query.size = (n : Int))
    (alignedVA : query.va.toNat % n = 0)
    (pa : BitVec 56) (mapped : mapping query.va = some pa.toNat)
    (mmio : MemM1.MemReadIF.NotMMIO pa) (value : BitVec (n * 8)) :
    ∃ address translated final, ∃ faultOut : FaultRecord,
      CleanTranslateResultFields spec config rows mapping query data.leafLevel data.view initial
        (faultOut, address) translated ∧
      CurrentS1At spec config rows translated ∧
      CurrentS1AccessAt spec config rows mapping query data translated ∧
      TranslateEventsAt spec query data.leafLevel initial address translated ∧
      Mem_set query.va n query.request.raw value initial = .ok () final ∧
      final.events = translated.events.push (.memWrite pa.toNat n (some address.vaddress.toNat)
        (AccessDescriptor_to_Access_kind query.request.raw)
        (some (Sail.BitVec.castWidth (m := 8 * n) value)) none) ∧
      final.regs = translated.regs ∧
      final.mem = MemM1.MemWriteD1.wfold translated.mem pa.toNat n
        (fun j => (Sail.BitVec.castWidth (m := 8 * n) value).extractLsb' (8 * j) 8) := by
  obtain ⟨address, translated, final, ⟨faultOut, clean, currentT, accessT, eventsT⟩, call, events, regs, mem⟩ :=
    MemM1.MemWriteD6.memset_skelT query.va n sizeOK alignedVA query.request.raw initial pa value shape
      pre.tag
      (fun address translated => ∃ faultOut : FaultRecord,
        CleanTranslateResultFields spec config rows mapping query data.leafLevel data.view initial
          (faultOut, address) translated ∧
        CurrentS1At spec config rows translated ∧
        CurrentS1AccessAt spec config rows mapping query data translated ∧
        TranslateEventsAt spec query data.leafLevel initial address translated)
      (by
        intro framed frame
        have frameRegs : framed.regs = initial.regs := frame.1
        have frameMem : framed.mem = initial.mem := frame.2.1
        obtain ⟨address, faultOut, other, translateCall, fields, currentO, accessO, _, _, _, _, _,
            _, _, info, walk, leaf, middle, walkLen, traffic, endEv, cond, wb, slots⟩ :=
          current_translate_address_events spec config rows mapping query member data framed
            (current_s1_frame current frameRegs frameMem) (access.of_regs frameRegs)
            (by rw [frameRegs]; exact mode) (by rw [frameRegs]; exact aa64)
            (by rw [frameRegs]; exact debug) (by rw [frameRegs]; exact spe)
        rw [alignedQ, sizeQ] at translateCall
        have cleanInitial := clean_translate_result_memory_frames spec config rows mapping query
          data.leafLevel data.view initial framed other other (faultOut, address) frameRegs frameMem
          rfl rfl fields
        have kept := fields
        obtain ⟨_, out, _, _, _, _, _, mapResult, _, _, addressFault, _, _, registers, _⟩ := kept
        have addressPA : address.paddress.address = pa :=
          BitVec.eq_of_toNat_eq (Option.some.inj (mapResult.symm.trans mapped))
        have regsEq : other.regs = initial.regs := by
          rw [registers, frameRegs]
          unfold fetchGuardRegs
          rw [shape.base.gpr]
          rfl
        refine ⟨address, other, translateCall, addressFault, addressPA, ?_, ?_,
          faultOut, cleanInitial, currentO, accessO,
          ⟨info, walk, leaf, middle, walkLen, by rw [← frame.2.2]; exact traffic, endEv,
            fun raw none => by
              obtain ⟨f1, f2, f3⟩ := cond (by rw [frameMem]; exact raw) (by rw [frameRegs]; exact none)
              exact ⟨f1, f2, f3.trans frameMem⟩,
            fun cached => wb (by rw [frameRegs]; exact cached), slots⟩⟩
        · rw [regsEq]; exact spe
        · unfold MemM1.MemWriteD5.TagOK; rw [regsEq]; exact pre.tag)
      mmio (MemM1.MemWriteD6.littleEndian_of _ _ shape pre)
  exact ⟨address, translated, final, faultOut, clean, currentT, accessT, eventsT, call, events, regs, mem⟩

theorem native_data_read8_events {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (query : AccessQuery) (member : domain query) (data : S1AccessData spec config rows query)
    (initial : State) (current : CurrentS1At spec config rows initial)
    (access : CurrentS1AccessAt spec config rows mapping query data initial)
    (mode : HostEL0ModeAt initial.regs) (aa64 : initial.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt initial.regs) (post : MemM1.MemReadD.PostRegs initial.regs)
    (shape : MemM1.MemReadD.AccDR query.request.raw)
    (alignedQ : query.request.aligned = true) (sizeQ : query.size = ((8 : Nat) : Int))
    (alignedVA : query.va.toNat % 8 = 0)
    (pa : BitVec 56) (mapped : mapping query.va = some pa.toNat)
    (mmio : MemM1.MemReadIF.NotMMIO pa)
    (word : BitVec 64) (bytes : ∀ i < 8, initial.mem[pa.toNat + i]? = some (word.extractLsb' (8 * i) 8))
    (outside : ∀ i < 8, ¬ (rowsFootprint spec.imageRows).byte (pa.toNat + i)) :
    ∃ address translated final, ∃ faultOut : FaultRecord,
      CleanTranslateResultFields spec config rows mapping query data.leafLevel data.view initial
        (faultOut, address) translated ∧
      CurrentS1At spec config rows translated ∧
      CurrentS1AccessAt spec config rows mapping query data translated ∧
      TranslateEventsAt spec query data.leafLevel initial address translated ∧
      Mem_read query.va 8 query.request.raw initial = .ok word final ∧
      final.events = translated.events.push (.memRead pa.toNat 8 (some address.vaddress.toNat)
        (AccessDescriptor_to_Access_kind query.request.raw) false) ∧
      final.regs = translated.regs ∧ final.mem = translated.mem := by
  obtain ⟨address, translated, final, ⟨faultOut, clean, currentT, accessT, eventsT⟩, call, events, regs, mem⟩ :=
    MemM1.MemReadD.memRead8 query.va alignedVA query.request.raw initial pa word shape
      (fun address translated => ∃ faultOut : FaultRecord,
        CleanTranslateResultFields spec config rows mapping query data.leafLevel data.view initial
          (faultOut, address) translated ∧
        CurrentS1At spec config rows translated ∧
        CurrentS1AccessAt spec config rows mapping query data translated ∧
        TranslateEventsAt spec query data.leafLevel initial address translated)
      (by
        intro framed frame
        have frameRegs : framed.regs = initial.regs := frame.1
        have frameMem : framed.mem = initial.mem := frame.2.1
        obtain ⟨address, faultOut, other, translateCall, fields, currentO, accessO, _, _, _, _, _,
            writes, _, info, walk, leaf, middle, walkLen, traffic, endEv, cond, wb, slots⟩ :=
          current_translate_address_events spec config rows mapping query member data framed
            (current_s1_frame current frameRegs frameMem) (access.of_regs frameRegs)
            (by rw [frameRegs]; exact mode) (by rw [frameRegs]; exact aa64)
            (by rw [frameRegs]; exact debug) (by rw [frameRegs]; exact post.spe)
        rw [alignedQ, sizeQ] at translateCall
        have cleanInitial := clean_translate_result_memory_frames spec config rows mapping query
          data.leafLevel data.view initial framed other other (faultOut, address) frameRegs frameMem
          rfl rfl fields
        have kept := fields
        obtain ⟨_, out, _, _, _, _, _, mapResult, _, _, addressFault, _, _, registers, _⟩ := kept
        have addressPA : address.paddress.address = pa :=
          BitVec.eq_of_toNat_eq (Option.some.inj (mapResult.symm.trans mapped))
        refine ⟨address, other, translateCall, addressFault, addressPA, ?_, ?_,
          faultOut, cleanInitial, currentO, accessO,
          ⟨info, walk, leaf, middle, walkLen, by rw [← frame.2.2]; exact traffic, endEv,
            fun raw none => by
              obtain ⟨f1, f2, f3⟩ := cond (by rw [frameMem]; exact raw) (by rw [frameRegs]; exact none)
              exact ⟨f1, f2, f3.trans frameMem⟩,
            fun cached => wb (by rw [frameRegs]; exact cached), slots⟩⟩
        · rw [registers, frameRegs]
          exact post_regs_data _ _ _ shape.gpr post
        · intro i hi
          have unchanged := writes _ (outside i hi)
          simp only at unchanged
          rw [unchanged, frameMem]
          exact bytes i hi)
      mmio
  exact ⟨address, translated, final, faultOut, clean, currentT, accessT, eventsT, call, events, regs, mem⟩

#print axioms native_data_read8_events
#print axioms native_data_read1_events
#print axioms native_data_write_events
end ArmCertWalk
