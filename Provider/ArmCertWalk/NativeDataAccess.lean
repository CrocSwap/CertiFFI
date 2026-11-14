-- payload step 2 on the generalized base, from the canonical invariant:
-- (a) actual 1-byte DATA read (canonical MemReadD.memRead1 on post-translation memory);
-- (b) actual DATA store Mem_set va n acc v, n ∈ {1,2,4,8,16} (canonical MemWriteD6.memset_skelT,
--     which writes onto the ACTUAL post-walk memory: t.mem = wfold translated.mem pa n bytes(v));
-- and paired forms carrying a caller relation (canonical EncodedRel instance) on the two words.
-- PostRegs/PreW bits are existing E1/E3(E0E)/E11/E19/F2(MTE2 off or untagged)/F6/F15.
import ArmCertWalk.NativeDataRead
import MemM1.MemWriteD6
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk

/-- Actual `Mem_read va 1 acc` (GPR byte load) from the canonical invariant. -/
theorem native_data_read1_current {domain : QueryDomain} (spec : TopologyImageSpec domain)
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
      Mem_read query.va 1 query.request.raw initial = .ok value final ∧
      final.events = translated.events.push (.memRead pa.toNat 1 (some address.vaddress.toNat)
        (AccessDescriptor_to_Access_kind query.request.raw) false) ∧
      final.regs = translated.regs ∧ final.mem = translated.mem := by
  obtain ⟨address, translated, final, ⟨faultOut, clean, currentT, accessT⟩, call, events, regs, mem⟩ :=
    MemM1.MemReadD.memRead1 query.va (Nat.mod_one _) query.request.raw initial pa value shape
      (fun address translated => ∃ faultOut : FaultRecord,
        CleanTranslateResultFields spec config rows mapping query data.leafLevel data.view initial
          (faultOut, address) translated ∧
        CurrentS1At spec config rows translated ∧
        CurrentS1AccessAt spec config rows mapping query data translated)
      (by
        intro framed frame
        have frameRegs : framed.regs = initial.regs := frame.1
        have frameMem : framed.mem = initial.mem := frame.2.1
        obtain ⟨address, faultOut, other, translateCall, fields, currentO, accessO, _, _, _, _, _,
            writes, _⟩ :=
          current_translate_address_total spec config rows mapping query member data framed
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
          faultOut, cleanInitial, currentO, accessO⟩
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
  exact ⟨address, translated, final, faultOut, clean, currentT, accessT, call, events, regs, mem⟩

/-- Actual `Mem_set va n acc v` (GPR store, n ∈ {1,2,4,8,16}, aligned) from the
canonical invariant. The store lands on the ACTUAL post-walk memory. -/
theorem native_data_write_current {domain : QueryDomain} (spec : TopologyImageSpec domain)
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
      Mem_set query.va n query.request.raw value initial = .ok () final ∧
      final.events = translated.events.push (.memWrite pa.toNat n (some address.vaddress.toNat)
        (AccessDescriptor_to_Access_kind query.request.raw)
        (some (Sail.BitVec.castWidth (m := 8 * n) value)) none) ∧
      final.regs = translated.regs ∧
      final.mem = MemM1.MemWriteD1.wfold translated.mem pa.toNat n
        (fun j => (Sail.BitVec.castWidth (m := 8 * n) value).extractLsb' (8 * j) 8) := by
  obtain ⟨address, translated, final, ⟨faultOut, clean, currentT, accessT⟩, call, events, regs, mem⟩ :=
    MemM1.MemWriteD6.memset_skelT query.va n sizeOK alignedVA query.request.raw initial pa value shape
      pre.tag
      (fun address translated => ∃ faultOut : FaultRecord,
        CleanTranslateResultFields spec config rows mapping query data.leafLevel data.view initial
          (faultOut, address) translated ∧
        CurrentS1At spec config rows translated ∧
        CurrentS1AccessAt spec config rows mapping query data translated)
      (by
        intro framed frame
        have frameRegs : framed.regs = initial.regs := frame.1
        have frameMem : framed.mem = initial.mem := frame.2.1
        obtain ⟨address, faultOut, other, translateCall, fields, currentO, accessO, _, _, _, _, _,
            _, _⟩ :=
          current_translate_address_total spec config rows mapping query member data framed
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
          faultOut, cleanInitial, currentO, accessO⟩
        · rw [regsEq]; exact spe
        · unfold MemM1.MemWriteD5.TagOK; rw [regsEq]; exact pre.tag)
      mmio (MemM1.MemWriteD6.littleEndian_of _ _ shape pre)
  exact ⟨address, translated, final, faultOut, clean, currentT, accessT, call, events, regs, mem⟩

/-- ** paired data store.** Two actual stores (bases B1/B2) with values
related by a caller relation (canonical EncodedRel) land on each side's actual
post-walk memory; the related values are exactly the stored payloads. -/
theorem paired_data_write_current {domain₁ domain₂ : QueryDomain}
    (spec₁ : TopologyImageSpec domain₁) (spec₂ : TopologyImageSpec domain₂)
    (config₁ config₂ : AttributeConfig) (rows₁ rows₂ : List PermissionRow)
    (mapping₁ mapping₂ : BitVec 64 → Option Nat) (query₁ query₂ : AccessQuery)
    (member₁ : domain₁ query₁) (member₂ : domain₂ query₂)
    (data₁ : S1AccessData spec₁ config₁ rows₁ query₁) (data₂ : S1AccessData spec₂ config₂ rows₂ query₂)
    (initial₁ initial₂ : State)
    (current₁ : CurrentS1At spec₁ config₁ rows₁ initial₁) (current₂ : CurrentS1At spec₂ config₂ rows₂ initial₂)
    (access₁ : CurrentS1AccessAt spec₁ config₁ rows₁ mapping₁ query₁ data₁ initial₁)
    (access₂ : CurrentS1AccessAt spec₂ config₂ rows₂ mapping₂ query₂ data₂ initial₂)
    (mode₁ : HostEL0ModeAt initial₁.regs) (mode₂ : HostEL0ModeAt initial₂.regs)
    (aa64₁ : initial₁.regs.FeatureImpl[4] = true) (aa64₂ : initial₂.regs.FeatureImpl[4] = true)
    (debug₁ : ExistingE11DebugAt initial₁.regs) (debug₂ : ExistingE11DebugAt initial₂.regs)
    (spe₁ : initial₁.regs.bank_Bool .SPESampleInFlight = false)
    (spe₂ : initial₂.regs.bank_Bool .SPESampleInFlight = false)
    (n : Nat) (sizeOK : MemM1.MemWriteD1.SizeOK n)
    (shape₁ : MemM1.MemWriteD5.AccDWT query₁.request.raw) (shape₂ : MemM1.MemWriteD5.AccDWT query₂.request.raw)
    (pre₁ : MemM1.MemWriteD6.PreW query₁.request.raw initial₁.regs)
    (pre₂ : MemM1.MemWriteD6.PreW query₂.request.raw initial₂.regs)
    (alignedQ₁ : query₁.request.aligned = true) (alignedQ₂ : query₂.request.aligned = true)
    (sizeQ₁ : query₁.size = (n : Int)) (sizeQ₂ : query₂.size = (n : Int))
    (alignedVA₁ : query₁.va.toNat % n = 0) (alignedVA₂ : query₂.va.toNat % n = 0)
    (pa₁ pa₂ : BitVec 56) (mapped₁ : mapping₁ query₁.va = some pa₁.toNat)
    (mapped₂ : mapping₂ query₂.va = some pa₂.toNat)
    (mmio₁ : MemM1.MemReadIF.NotMMIO pa₁) (mmio₂ : MemM1.MemReadIF.NotMMIO pa₂)
    (value₁ value₂ : BitVec (n * 8)) (Rel : BitVec (n * 8) → BitVec (n * 8) → Prop)
    (related : Rel value₁ value₂) :
    ∃ translated₁ final₁ translated₂ final₂,
      Mem_set query₁.va n query₁.request.raw value₁ initial₁ = .ok () final₁ ∧
      Mem_set query₂.va n query₂.request.raw value₂ initial₂ = .ok () final₂ ∧
      final₁.mem = MemM1.MemWriteD1.wfold translated₁.mem pa₁.toNat n
        (fun j => (Sail.BitVec.castWidth (m := 8 * n) value₁).extractLsb' (8 * j) 8) ∧
      final₂.mem = MemM1.MemWriteD1.wfold translated₂.mem pa₂.toNat n
        (fun j => (Sail.BitVec.castWidth (m := 8 * n) value₂).extractLsb' (8 * j) 8) ∧
      CurrentS1At spec₁ config₁ rows₁ translated₁ ∧ CurrentS1At spec₂ config₂ rows₂ translated₂ ∧
      Rel value₁ value₂ := by
  obtain ⟨_, translated₁, final₁, _, _, currentT₁, _, call₁, _, _, mem₁⟩ :=
    native_data_write_current spec₁ config₁ rows₁ mapping₁ query₁ member₁ data₁ initial₁ current₁
      access₁ mode₁ aa64₁ debug₁ spe₁ n sizeOK shape₁ pre₁ alignedQ₁ sizeQ₁ alignedVA₁ pa₁ mapped₁
      mmio₁ value₁
  obtain ⟨_, translated₂, final₂, _, _, currentT₂, _, call₂, _, _, mem₂⟩ :=
    native_data_write_current spec₂ config₂ rows₂ mapping₂ query₂ member₂ data₂ initial₂ current₂
      access₂ mode₂ aa64₂ debug₂ spe₂ n sizeOK shape₂ pre₂ alignedQ₂ sizeQ₂ alignedVA₂ pa₂ mapped₂
      mmio₂ value₂
  exact ⟨translated₁, final₁, translated₂, final₂, call₁, call₂, mem₁, mem₂, currentT₁, currentT₂,
    related⟩

#print axioms native_data_read1_current
#print axioms native_data_write_current
#print axioms paired_data_write_current
end ArmCertWalk
