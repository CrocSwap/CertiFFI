import ArmCertWalk.NativeTranslateLoop
import ArmCertTranslateModel.CurrentControlTransport

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- The existing host bundle observes registers only. -/
theorem host_walk_at_regs_frame {config : AttributeConfig} {controls : S1LogicalReference.Controls}
    {physicalConfig : PhysicalConfig} {before after : State}
    (current : HostWalkAt config controls physicalConfig before)
    (registers : after.regs = before.regs) : HostWalkAt config controls physicalConfig after := by
  refine ⟨current.regime.of_regs registers, ?_, current.physical.of_regs registers, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [registers]
  · exact current.controls
  · exact current.ips
  · exact current.endian
  · exact current.mair
  · exact current.xs
  · exact current.mte2
  · exact current.el

theorem host_walk_at_guarded_page {config : AttributeConfig} {controls : S1LogicalReference.Controls}
    {physicalConfig : PhysicalConfig} {state : State}
    (current : HostWalkAt config controls physicalConfig state) (guarded : Bool) :
    HostWalkAt config controls physicalConfig {state with regs := gpRegs state.regs guarded} :=
  ⟨HostRegimeAt.guarded_page state current.regime guarded, current.controls.guarded_page guarded,
    physical_at_register_fields current.physical rfl rfl, current.ips, current.endian, current.mair,
    current.xs, current.mte2, current.el⟩

/-- Consume the PAST actual loop's register conclusion. Together with its
    source-derived CurrentImages result this preserves the current inputs for
    later accesses, including real guarded-page=true and false IFETCH results. -/
theorem translate_loop_register_bindings {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (mapping : BitVec 64 → Option Nat) (query : AccessQuery)
    (level : Nat) (view : S1DescriptorPIE.View 64) (before after : State) (next : TTWState)
    (registers : after.regs = fetchGuardRegs query.request.raw next before.regs)
    (current : HostWalkAt config spec.controls spec.physicalConfig before)
    (bound : HostImageParamsAt before.regs spec.params)
    (layout : CurrentLayoutAt spec.layout spec.params query.va before.regs)
    (map : LeafMapAt mapping spec.physicalConfig before.regs query level view) :
    HostWalkAt config spec.controls spec.physicalConfig after ∧
    HostImageParamsAt after.regs spec.params ∧ CurrentLayoutAt spec.layout spec.params query.va after.regs ∧
    LeafMapAt mapping spec.physicalConfig after.regs query level view := by
  have guarded : HostWalkAt config spec.controls spec.physicalConfig (fetchGuardState query.request.raw next before) ∧
      HostImageParamsAt (fetchGuardRegs query.request.raw next before.regs) spec.params ∧
      CurrentLayoutAt spec.layout spec.params query.va (fetchGuardRegs query.request.raw next before.regs) ∧
      LeafMapAt mapping spec.physicalConfig (fetchGuardRegs query.request.raw next before.regs) query level view := by
    unfold fetchGuardState fetchGuardRegs
    by_cases fetch : query.request.raw.acctype == .AccessType_IFETCH
    · simp only [fetch, ↓reduceIte]
      exact ⟨host_walk_at_guarded_page current _, bound.guarded_page _,
        current_layout_guarded_page layout _, map.guarded_page _⟩
    · simp only [fetch, ↓reduceIte]
      exact ⟨current, bound, layout, map⟩
  refine ⟨host_walk_at_regs_frame guarded.1 registers, ?_, ?_, ?_⟩
  all_goals rw [registers]
  · exact guarded.2.1
  · exact guarded.2.2.1
  · exact guarded.2.2.2

/-- Extend the ACTUAL native translation-loop result with preservation of the
    existing current host, parameter, layout and map predicates. No future
    preservation callback or alternate execution engine is used. Outer
    S1Translate/TranslateAddress/run composition remains a separate obligation. -/
theorem native_translate_loop_current_total {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (query : AccessQuery) (member : domain query) (aligned : Bool)
    (leafLevel logical : Nat) (physical : FullAddress) (view : S1DescriptorPIE.View 64)
    (path : S1LogicalReference.Path (logicalObserve spec.logicalRows)
      (effectiveBits spec.physicalConfig).toNat query.va spec.layout.start
      (S1LogicalReference.rootBits spec.layout.start spec.layout.inputBits) spec.layout.root
      (.leaf leafLevel logical physical view))
    (binding : PathPermissionUse spec config rows query path ⟨0#2, false, false⟩)
    (oldAccess : AccessDescriptor) (oldSlot : AddressDescriptor) (oldDescriptor : BitVec 128)
    (fault : FaultRecord) (oldMemory oldNew : BitVec 128) (a64 s2 : Bool) (oldNext : TTWState) (initial : State)
    (format : WalkFormat spec.params spec.physicalConfig spec.controls)
    (callees : WalkCalleesAt spec.params spec.physicalConfig spec.controls config initial)
    (images : CurrentImagesAt spec config rows initial)
    (layout : CurrentLayoutAt spec.layout spec.params query.va initial.regs)
    (disch : spec.params.disch = 0#1) (accessEL : query.request.raw.el = EL0)
    (ss : query.request.raw.ss = .SS_NonSecure) (noFault : fault.statuscode = .Fault_None)
    (cache : initial.regs.bank_Bool .__tlb_enabled = false)
    (epd : currentWalkEPD initial.regs query.va = 0#1)
    (map : LeafMapAt mapping spec.physicalConfig initial.regs query leafLevel view)
    (current : HostWalkAt config spec.controls spec.physicalConfig initial)
    (bound : HostImageParamsAt initial.regs spec.params) :
    ∃ (out : TranslateVars) (other : State) (operations : List TableUpdate),
      S1WalkSource.translate.loop0 .Regime_EL20 query.va aligned query.request.raw oldAccess a64 s2 fault
        spec.params oldSlot oldNext oldDescriptor oldNew oldMemory initial = .ok (.ok out) other ∧
      translateStop out = true ∧ (translateFault out).statuscode = .Fault_None ∧
      (translateCurrent out).level = (leafLevel : Int) ∧
      (translateSlot out).paddress = physical ∧ (translateSlot out).vaddress = query.va ∧
      (translateCurrent out).memattrs.memtype = .MemType_Normal ∧
      mapping query.va = some (S1LogicalReference.outputAddress query.va leafLevel
        (translateCurrent out).baseaddress ((translateCurrent out).contiguous == 1#1)).address.toNat ∧
      other.regs = fetchGuardRegs query.request.raw (translateCurrent out) initial.regs ∧
      StoreHistory spec.params (rowsFootprint spec.imageRows) initial.mem operations other.mem ∧
      CurrentImagesAt spec config rows other ∧
      HostWalkAt config spec.controls spec.physicalConfig other ∧
      HostImageParamsAt other.regs spec.params ∧ CurrentLayoutAt spec.layout spec.params query.va other.regs ∧
      LeafMapAt mapping spec.physicalConfig other.regs query leafLevel view := by
  obtain ⟨out, other, operations, call, stop, faultNone, level, slotPA, slotVA, normal, mapResult,
    registers, history, afterImages⟩ :=
    native_translate_loop_total spec config rows mapping query member aligned leafLevel logical physical view
      path binding oldAccess oldSlot oldDescriptor fault oldMemory oldNew a64 s2 oldNext initial format callees
      images layout disch accessEL ss noFault cache epd map
  have preserved := translate_loop_register_bindings spec config mapping query leafLevel view initial other
    (translateCurrent out) registers current bound layout map
  exact ⟨out, other, operations, call, stop, faultNone, level, slotPA, slotVA, normal, mapResult,
    registers, history, afterImages, preserved⟩

#print axioms host_walk_at_regs_frame
#print axioms host_walk_at_guarded_page
#print axioms translate_loop_register_bindings
#print axioms native_translate_loop_current_total
end ArmCert.Translate.Model
