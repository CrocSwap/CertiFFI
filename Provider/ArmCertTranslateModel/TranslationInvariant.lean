import ArmCertTranslateModel.NativeTranslateBinding

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- The existing current image and primitive host/getter inputs, collected for
    run composition. Every field concerns the CURRENT state. There is no
    future-call, membership, preservation, observation or scheduler field. -/
structure CurrentS1At {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (state : State) : Prop where
  images : CurrentImagesAt spec config rows state
  host : HostWalkAt config spec.controls spec.physicalConfig state
  core : HostImageParamsAt state.regs
    {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (state.regs.bank_BitVec_64 .TCR_EL2)}
  geometry : spec.params.txsz = normalizeTxsz state.regs
    (_get_TCR_EL2_Type_T0SZ (state.regs.bank_BitVec_64 .TCR_EL2))
  guards : HostTranslateGuardAt state.regs spec.params
  rawFault : sourceTxszFault state.regs
    {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (state.regs.bank_BitVec_64 .TCR_EL2)} = false
  enabled : currentTranslationEnabled state.regs = true
  cache : state.regs.bank_Bool .__tlb_enabled = false

/-- Finite certificate DATA on the already existing Path. This supplies no
    native execution or future success answer. The actual query keeps its full
    access descriptor, alignment flag and size. -/
structure S1AccessData {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (query : AccessQuery) where
  leafLevel : Nat
  logical : Nat
  physical : FullAddress
  view : S1DescriptorPIE.View 64
  path : S1LogicalReference.Path (logicalObserve spec.logicalRows)
    (effectiveBits spec.physicalConfig).toNat query.va spec.layout.start
    (S1LogicalReference.rootBits spec.layout.start spec.layout.inputBits) spec.layout.root
    (.leaf leafLevel logical physical view)
  permissions : PathPermissionUse spec config rows query path ⟨0#2, false, false⟩
  lower : AArch64_GetVARange query.va = .VARange_LOWER
  accessEL : query.request.raw.el = EL0
  nonsecure : query.request.raw.ss = .SS_NonSecure

/-- Existing pure current-state checks for this actual access certificate.
    This is not an assumption that a later access will belong to the domain. -/
structure CurrentS1AccessAt {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (query : AccessQuery) (data : S1AccessData spec config rows query) (state : State) : Prop where
  layout : CurrentLayoutAt spec.layout spec.params query.va state.regs
  checks : TranslateQueryChecks state.regs spec.params query.va query.request.raw
  epd : currentWalkEPD state.regs query.va = 0#1
  map : LeafMapAt mapping spec.physicalConfig state.regs query data.leafLevel data.view
  outputPolicy : OutputCacheAdmissible query.request.raw state.regs

theorem CurrentS1AccessAt.of_regs {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {query : AccessQuery} {data : S1AccessData spec config rows query} {before after : State}
    (access : CurrentS1AccessAt spec config rows mapping query data before)
    (registers : after.regs = before.regs) : CurrentS1AccessAt spec config rows mapping query data after := by
  refine ⟨access.layout.of_regs registers, ?_, ?_, ?_, ?_⟩
  all_goals rw [registers]
  · exact access.checks
  · exact access.epd
  · exact access.map
  · exact access.outputPolicy

theorem CurrentS1AccessAt.guarded_page {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {query : AccessQuery} {data : S1AccessData spec config rows query} {state : State}
    (access : CurrentS1AccessAt spec config rows mapping query data state) (guarded : Bool) :
    CurrentS1AccessAt spec config rows mapping query data {state with regs := gpRegs state.regs guarded} :=
  ⟨current_layout_guarded_page access.layout guarded,
    translate_query_checks_register_fields access.checks rfl, access.epd,
    access.map.guarded_page guarded, access.outputPolicy⟩

/-- A translation of ONE actual query preserves the primitive checks of ANY
    other declared query. This transports current data, not future membership
    or future success. Its memory may have changed at descriptor flag bytes. -/
theorem CurrentS1AccessAt.after_translate {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {actualQuery query : AccessQuery} {leafLevel : Nat} {view : S1DescriptorPIE.View 64}
    {data : S1AccessData spec config rows query} {initial other : State}
    {result : FaultRecord × AddressDescriptor}
    (access : CurrentS1AccessAt spec config rows mapping query data initial)
    (clean : CleanTranslateResult spec config rows mapping actualQuery leafLevel view initial result other) :
    CurrentS1AccessAt spec config rows mapping query data other := by
  obtain ⟨params, out, operations, active, faultEq, faultNone, mapResult, va, normal, pa,
    registers, history, images, held⟩ := clean
  have fetch : CurrentS1AccessAt spec config rows mapping query data
      (fetchGuardState actualQuery.request.raw (translateCurrent out) initial) := by
    unfold fetchGuardState fetchGuardRegs
    split
    · exact access.guarded_page _
    · exact access
  exact fetch.of_regs registers

/-- The PAST actual complete S1Translate result preserves these current-state
    inputs. This constructor is internal to the derived native result; callers
    do not supply a future invariant-preservation rule. -/
theorem current_s1_after {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {query : AccessQuery} (data : S1AccessData spec config rows query)
    {initial other : State} {result : FaultRecord × AddressDescriptor}
    (current : CurrentS1At spec config rows initial)
    (access : CurrentS1AccessAt spec config rows mapping query data initial)
    (clean : CleanTranslateResult spec config rows mapping query data.leafLevel data.view initial result other) :
    CurrentS1At spec config rows other ∧ CurrentS1AccessAt spec config rows mapping query data other := by
  have frames := clean_translate_image_frame clean
  obtain ⟨params, out, operations, active, faultEq, faultNone, mapResult, va, normal, pa,
    registers, history, images, held⟩ := clean
  obtain ⟨hostAfter, coreAfter, geometryAfter, layoutAfter, mapAfter, guardAfter, checksAfter, faultAfter⟩ :=
    normalized_translate_register_bindings spec config mapping query data.leafLevel data.view initial other
      (translateCurrent out) registers current.host current.core current.geometry access.layout access.map
      current.guards access.checks current.rawFault
  have sameSCTLR : other.regs.bank_BitVec_64 .SCTLR_EL2 = initial.regs.bank_BitVec_64 .SCTLR_EL2 := by
    rw [registers]; unfold fetchGuardRegs; split <;> rfl
  have sameTCR : other.regs.bank_BitVec_64 .TCR_EL2 = initial.regs.bank_BitVec_64 .TCR_EL2 := by
    rw [registers]; unfold fetchGuardRegs; split <;> rfl
  refine ⟨⟨frames.1, hostAfter, coreAfter, geometryAfter, guardAfter, faultAfter, ?_, ?_⟩,
    ⟨layoutAfter, checksAfter, ?_, mapAfter, ?_⟩⟩
  · simpa only [currentTranslationEnabled, sameSCTLR] using current.enabled
  · rw [registers]; unfold fetchGuardRegs; split <;> exact current.cache
  · simpa only [currentWalkEPD, sameTCR] using access.epd
  · rw [registers]; unfold fetchGuardRegs; split <;> exact access.outputPolicy

/-- Structural current data derives the actual complete S1Translate call,
    canonical partial-map agreement, preserved current inputs and native memory
    frames on ONE actual successor. It uses the query's actual alignment flag.
    The full outer TranslateAddress/fetch/run theorem remains a separate join. -/
theorem current_s1_translate_total {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (query : AccessQuery) (member : domain query) (data : S1AccessData spec config rows query)
    (fault : FaultRecord) (initial : State) (current : CurrentS1At spec config rows initial)
    (access : CurrentS1AccessAt spec config rows mapping query data initial)
    (noFault : fault.statuscode = .Fault_None) :
    ∃ result other,
      AArch64_S1Translate fault .Regime_EL20 query.va query.request.aligned query.request.raw initial =
        .ok result other ∧
      CleanTranslateResult spec config rows mapping query data.leafLevel data.view initial result other ∧
      CurrentS1At spec config rows other ∧ CurrentS1AccessAt spec config rows mapping query data other ∧
      ArmCert.Premises.TranslationAgreesV1.ProjRegsEq initial.regs other.regs ∧
      WritesOnly (rowsFootprint spec.imageRows).byte (fun a => initial.mem[a]?) (fun a => other.mem[a]?) ∧
      (∀ address : Nat, (other.mem[address]?).isSome = (initial.mem[address]?).isSome) := by
  obtain ⟨result, other, call, clean⟩ :=
    native_translate_total spec config rows mapping query member query.request.aligned data.leafLevel
      data.logical data.physical data.view data.path data.permissions fault initial data.lower current.host
      current.core current.geometry access.layout current.images current.guards access.checks current.rawFault
      current.enabled data.accessEL data.nonsecure noFault current.cache access.epd access.map access.outputPolicy
  have preserved := current_s1_after data current access clean
  have frames := clean_translate_image_frame clean
  exact ⟨result, other, call, clean, preserved.1, preserved.2, frames.2⟩

#print axioms CurrentS1AccessAt.of_regs
#print axioms CurrentS1AccessAt.guarded_page
#print axioms CurrentS1AccessAt.after_translate
#print axioms current_s1_after
#print axioms current_s1_translate_total
end ArmCert.Translate.Model
