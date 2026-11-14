import ArmCertWalk.TranslateChoiceInputs
import ArmCertWalk.StageCanonical

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

/-- Complete actual post-loop S1Translate continuation, including the SECOND
source StageOA, real undefined-attribute occurrence, actual I/D-cache and tag
choices, LS64 check, address constructor and MECID. Normal output attributes
may be NC; the exact chosen attributes are retained in the returned address. -/
theorem native_translate_suffix_total (params : S1TTWParams) (va : BitVec 64) (acc oldAccess : AccessDescriptor)
    (slot : AddressDescriptor) (descriptor : BitVec 128) (fault : FaultRecord) (memDescriptor newDescriptor : BitVec 128)
    (a64 s2 : Bool) (next : TTWState) (level : Nat) (initial : State)
    (d128 : params.d128 = 0#1) (tg : params.tgx = .TGx_4KB)
    (positive : 1 ≤ level) (valid : level ≤ 3) (currentLevel : next.level = (level : Int))
    (nonsecure : next.baseaddress.paspace = .PAS_NonSecure)
    (normal : next.memattrs.memtype = .MemType_Normal) (noFault : fault.statuscode = .Fault_None)
    (cache : initial.regs.bank_Bool .__tlb_enabled = false)
    (outputPolicy : OutputCacheAdmissible acc initial.regs) :
    ∃ address other,
      TranslateFinishSource.suffix .Regime_EL20 va acc params
        (oldAccess, slot, descriptor, fault, memDescriptor, newDescriptor, a64, s2, next) initial =
        .ok (.ok (fault, address)) other ∧
      address.paddress = S1LogicalReference.outputAddress va level next.baseaddress (next.contiguous == 1#1) ∧
      address.vaddress = va ∧ address.memattrs.memtype = .MemType_Normal ∧
      address.tlbcontext = slot.tlbcontext ∧ address.s1assured = next.s1assured ∧ address.mecid = DEFAULT_MECID ∧
      other.regs = initial.regs ∧ other.mem = initial.mem ∧ other.events = initial.events := by
  have cacheCall := translate_cache_disabled descriptor memDescriptor newDescriptor initial cache
  obtain ⟨oa, afterStage, stageCall, space, value, stageRegs, stageMem, stageEvents⟩ :=
    stage_canonical_total va next level initial params d128 tg positive valid currentLevel
  let k := afterStage.choiceOcc.getD 1622 0
  let afterLabel : State := {afterStage with choiceOcc := afterStage.choiceOcc.insert 1622 (k + 1)}
  have labelCall : occLabel 1622 afterStage = .ok (.occ 1622 k) afterLabel := rfl
  obtain ⟨unused, ready, undefinedCall, undefinedRegs, undefinedMem, undefinedEvents⟩ :=
    undefined_attrs_normal (.occ 1622 k) afterLabel
  have readyRegs : ready.regs = initial.regs := undefinedRegs.trans stageRegs
  have readyMem : ready.mem = initial.mem := undefinedMem.trans stageMem
  have readyEvents : ready.events = initial.events := undefinedEvents.trans stageEvents
  obtain ⟨attrs, selected, selectionCall, selectionFrame, selectedNormal, exclusive⟩ :=
    output_attrs_admissible_total acc next ready normal (by rw [readyRegs]; exact outputPolicy)
  obtain ⟨address, other, finishCall, addressPA, addressVA, addressAttrs, context, assured, mecid,
    registers, memory, events⟩ :=
    output_finish_total va acc params slot descriptor fault next oa attrs selected (space.trans nonsecure) selectedNormal exclusive
  have addressNormal : address.memattrs.memtype = .MemType_Normal := by
    rw [addressAttrs]
    exact selectedNormal
  have canonicalSpace :
      (S1LogicalReference.outputAddress va level next.baseaddress (next.contiguous == 1#1)).paspace =
        next.baseaddress.paspace := rfl
  have fullValue : oa = S1LogicalReference.outputAddress va level next.baseaddress (next.contiguous == 1#1) := by
    have spaceEqual := space.trans canonicalSpace.symm
    cases oa with
    | mk actualSpace actualAddress =>
      cases expected : S1LogicalReference.outputAddress va level next.baseaddress (next.contiguous == 1#1) with
      | mk expectedSpace expectedAddress =>
        simp only [expected] at spaceEqual value ⊢
        congr <;> assumption
  refine ⟨address, other, ?_, addressPA.trans fullValue, addressVA, addressNormal, context, assured, mecid,
    registers.trans (selectionFrame.1.trans readyRegs), memory.trans (selectionFrame.2.1.trans readyMem),
    events.trans (selectionFrame.2.2.trans readyEvents)⟩
  rw [TranslateOutputParts.equation]
  have noneNe : ((.Fault_None : Fault) != .Fault_None) = false := rfl
  have notDevice : ((.MemType_Normal : MemType) == .MemType_Device) = false := rfl
  by_cases fetch : acc.acctype == .AccessType_IFETCH
  all_goals
    have selectedCall := selectionCall
    simp only [instructionOutputNC, fetch, Bool.false_eq_true, ↓reduceIte] at selectedCall
    have icacheCall := icache_el20_eq ready
    simp [TranslateOutputParts.withParts, cacheCall, noFault, noneNe, stageCall,
      labelCall, undefinedCall, normal, notDevice, fetch, icacheCall, selectedCall, finishCall,
      Bind.bind, Pure.pure, Functor.map, ExceptT.bind, ExceptT.bindCont, ExceptT.pure,
      ExceptT.mk, ExceptT.lift, EStateM.bind, EStateM.map, EStateM.pure,
      liftM, MonadLiftT.monadLift, MonadLift.monadLift]

#print axioms native_translate_suffix_total
end ArmCertWalk
