-- data payload, step 1: actual aligned 8-byte DATA read (Mem_read a 8 acc) on the
-- generalized base, from the canonical invariant. Translation is
-- current_translate_address_total at each actual framed prefix state; the read value is the
-- actual POST-WALK bytes at the actual PA, equal to the initial word because the slot lies
-- outside the table footprint (only footprint bytes can change). Canonical MemReadD.memRead8
-- already reads post-translation memory. PostRegs bits are existing E1/E3(E0E)/E11/E19/F6/F15.
-- Paired form: a caller relation Rel (canonical instance ArmCertCTD131.EncodedRel, per
-- /Core agreement) on the two INITIAL words transfers to the two actual read values.
import ArmCertWalk.NativeFetchPreserving
import MemM1.MemReadD
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk

theorem post_regs_data (acc : AccessDescriptor) (next : TTWState) (regs : Regs)
    (gpr : acc.acctype = .AccessType_GPR) (post : MemM1.MemReadD.PostRegs regs) :
    MemM1.MemReadD.PostRegs (fetchGuardRegs acc next regs) := by
  unfold fetchGuardRegs
  rw [gpr]
  exact post

/-- Actual `Mem_read va 8 acc` for a declared aligned GPR data query, from the
canonical invariant. Returns the INITIAL word at the mapped PA (slot outside the
table footprint), and the invariant on the actual translated state. -/
theorem native_data_read8_current {domain : QueryDomain} (spec : TopologyImageSpec domain)
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
      Mem_read query.va 8 query.request.raw initial = .ok word final ∧
      final.events = translated.events.push (.memRead pa.toNat 8 (some address.vaddress.toNat)
        (AccessDescriptor_to_Access_kind query.request.raw) false) ∧
      final.regs = translated.regs ∧ final.mem = translated.mem := by
  obtain ⟨address, translated, final, ⟨faultOut, clean, currentT, accessT⟩, call, events, regs, mem⟩ :=
    MemM1.MemReadD.memRead8 query.va alignedVA query.request.raw initial pa word shape
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
          have unchanged := writes _ (outside i hi)
          simp only at unchanged
          rw [unchanged, frameMem]
          exact bytes i hi)
      mmio
  exact ⟨address, translated, final, faultOut, clean, currentT, accessT, call, events, regs, mem⟩

/-- ** paired data payload.** Two actual 8-byte reads (bases B1/B2) return
their INITIAL words; any caller relation on the initial words (canonical:
shared-origin EncodedRel) holds of the two actual read values. -/
theorem paired_data_read8_current {domain₁ domain₂ : QueryDomain}
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
    (post₁ : MemM1.MemReadD.PostRegs initial₁.regs) (post₂ : MemM1.MemReadD.PostRegs initial₂.regs)
    (shape₁ : MemM1.MemReadD.AccDR query₁.request.raw) (shape₂ : MemM1.MemReadD.AccDR query₂.request.raw)
    (alignedQ₁ : query₁.request.aligned = true) (alignedQ₂ : query₂.request.aligned = true)
    (sizeQ₁ : query₁.size = ((8 : Nat) : Int)) (sizeQ₂ : query₂.size = ((8 : Nat) : Int))
    (alignedVA₁ : query₁.va.toNat % 8 = 0) (alignedVA₂ : query₂.va.toNat % 8 = 0)
    (pa₁ pa₂ : BitVec 56) (mapped₁ : mapping₁ query₁.va = some pa₁.toNat)
    (mapped₂ : mapping₂ query₂.va = some pa₂.toNat)
    (mmio₁ : MemM1.MemReadIF.NotMMIO pa₁) (mmio₂ : MemM1.MemReadIF.NotMMIO pa₂)
    (word₁ word₂ : BitVec 64)
    (bytes₁ : ∀ i < 8, initial₁.mem[pa₁.toNat + i]? = some (word₁.extractLsb' (8 * i) 8))
    (bytes₂ : ∀ i < 8, initial₂.mem[pa₂.toNat + i]? = some (word₂.extractLsb' (8 * i) 8))
    (outside₁ : ∀ i < 8, ¬ (rowsFootprint spec₁.imageRows).byte (pa₁.toNat + i))
    (outside₂ : ∀ i < 8, ¬ (rowsFootprint spec₂.imageRows).byte (pa₂.toNat + i))
    (Rel : BitVec 64 → BitVec 64 → Prop) (related : Rel word₁ word₂) :
    ∃ value₁ final₁ value₂ final₂,
      Mem_read query₁.va 8 query₁.request.raw initial₁ = .ok value₁ final₁ ∧
      Mem_read query₂.va 8 query₂.request.raw initial₂ = .ok value₂ final₂ ∧
      Rel value₁ value₂ := by
  obtain ⟨_, _, final₁, _, _, _, _, call₁, _⟩ :=
    native_data_read8_current spec₁ config₁ rows₁ mapping₁ query₁ member₁ data₁ initial₁ current₁
      access₁ mode₁ aa64₁ debug₁ post₁ shape₁ alignedQ₁ sizeQ₁ alignedVA₁ pa₁ mapped₁ mmio₁ word₁
      bytes₁ outside₁
  obtain ⟨_, _, final₂, _, _, _, _, call₂, _⟩ :=
    native_data_read8_current spec₂ config₂ rows₂ mapping₂ query₂ member₂ data₂ initial₂ current₂
      access₂ mode₂ aa64₂ debug₂ post₂ shape₂ alignedQ₂ sizeQ₂ alignedVA₂ pa₂ mapped₂ mmio₂ word₂
      bytes₂ outside₂
  exact ⟨word₁, final₁, word₂, final₂, call₁, call₂, related⟩

#print axioms native_data_read8_current
#print axioms paired_data_read8_current
end ArmCertWalk
