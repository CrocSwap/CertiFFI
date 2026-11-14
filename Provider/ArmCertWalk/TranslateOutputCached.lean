-- v3 ask (b): with the current S1 I/D caches ENABLED for the access kind, the actual
-- S1Translate output-attribute selection keeps the walk's memory attributes (no NormalNC
-- replacement), so the final address carries the walk leaf's inner/outer cacheability.
import ArmCertWalk.TranslateCacheAttrs
import ArmCertWalk.NativeTranslateSuffixFields
import ArmCertWalk.TranslateAlignment

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk
open S1NormalME

/-- Current S1 cache enable for the access kind (EL20: SCTLR_EL2.I for IFETCH, .C otherwise). -/
def outputCached (acc : AccessDescriptor) (regs : Regs) : Bool :=
  if acc.acctype == .AccessType_IFETCH then currentICache regs else currentDCache regs

theorem output_cached_gp (acc : AccessDescriptor) (next : TTWState) (regs : Regs) :
    outputCached acc (fetchGuardRegs acc next regs) = outputCached acc regs := by
  unfold fetchGuardRegs
  split <;> rfl

theorem output_cached_ordinary (acc : AccessDescriptor) (regs : Regs)
    (cached : outputCached acc regs = true) (policy : OutputCacheAdmissible acc regs) :
    acc.ls64 = false := by
  cases ls : acc.ls64 with
  | false => rfl
  | true =>
    have := policy ls
    unfold outputCached at cached
    split at this <;> simp_all

theorem selection_cached (acc : AccessDescriptor) (next : TTWState) (state : State)
    (normal : next.memattrs.memtype = .MemType_Normal) (cached : outputCached acc state.regs = true) :
    TranslateOutputParts.selection .Regime_EL20 acc next (instructionOutputNC acc state.regs) state =
      .ok (.ok next.memattrs) state := by
  have isNormal : ((.MemType_Normal : MemType) == .MemType_Normal) = true := rfl
  have notDevice : ((.MemType_Normal : MemType) == .MemType_Device) = false := rfl
  unfold TranslateOutputParts.selection
  by_cases fetch : acc.acctype == .AccessType_IFETCH
  · have icache : currentICache state.regs = true := by simpa [outputCached, fetch] using cached
    have notOrdinary : (acc.acctype != .AccessType_IFETCH) = false := by
      change (!(acc.acctype == .AccessType_IFETCH)) = false
      simp only [fetch, Bool.not_true]
    simp [instructionOutputNC, fetch, notOrdinary, icache, normal, notDevice, Bind.bind, Pure.pure,
      ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.lift,
      EStateM.bind, EStateM.map, EStateM.pure, liftM, MonadLiftT.monadLift, MonadLift.monadLift]
  · have dcache : currentDCache state.regs = true := by simpa [outputCached, fetch] using cached
    have ordinary : (acc.acctype != .AccessType_IFETCH) = true := by
      change (!(acc.acctype == .AccessType_IFETCH)) = true
      simp only [fetch, Bool.not_false]
    have cacheCall := dcache_el20_eq state
    rw [dcache] at cacheCall
    simp [instructionOutputNC, fetch, ordinary, normal, isNormal, cacheCall, Bind.bind, Pure.pure,
      Functor.map, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.lift,
      EStateM.bind, EStateM.map, EStateM.pure, liftM, MonadLiftT.monadLift, MonadLift.monadLift]

#print axioms selection_cached

/-- Sibling of `native_translate_suffix_fields_total`: with caches enabled for the access
kind, the actual final address keeps the walk state's inner/outer attributes. -/
theorem native_translate_suffix_cached (params : S1TTWParams) (va : BitVec 64) (acc oldAccess : AccessDescriptor)
    (slot : AddressDescriptor) (descriptor : BitVec 128) (fault : FaultRecord) (memDescriptor newDescriptor : BitVec 128)
    (a64 s2 : Bool) (next : TTWState) (level : Nat) (initial : State)
    (d128 : params.d128 = 0#1) (tg : params.tgx = .TGx_4KB)
    (positive : 1 ≤ level) (valid : level ≤ 3) (currentLevel : next.level = (level : Int))
    (nonsecure : next.baseaddress.paspace = .PAS_NonSecure)
    (normal : next.memattrs.memtype = .MemType_Normal) (noFault : fault.statuscode = .Fault_None)
    (cache : initial.regs.bank_Bool .__tlb_enabled = false)
    (outputPolicy : OutputCacheAdmissible acc initial.regs)
    (cached : outputCached acc initial.regs = true) :
    ∃ address other,
      TranslateFinishSource.suffix .Regime_EL20 va acc params
        (oldAccess, slot, descriptor, fault, memDescriptor, newDescriptor, a64, s2, next) initial =
        .ok (.ok (fault, address)) other ∧
      address.memattrs.inner = next.memattrs.inner ∧ address.memattrs.outer = next.memattrs.outer := by
  have cacheCall := translate_cache_disabled descriptor memDescriptor newDescriptor initial cache
  obtain ⟨oa, afterStage, stageCall, space, value, stageRegs, stageMem, stageEvents⟩ :=
    stage_canonical_total va next level initial params d128 tg positive valid currentLevel
  let k := afterStage.choiceOcc.getD 1622 0
  let afterLabel : State := {afterStage with choiceOcc := afterStage.choiceOcc.insert 1622 (k + 1)}
  have labelCall : occLabel 1622 afterStage = .ok (.occ 1622 k) afterLabel := rfl
  obtain ⟨unused, ready, undefinedCall, undefinedRegs, undefinedMem, undefinedEvents⟩ :=
    undefined_attrs_normal (.occ 1622 k) afterLabel
  have readyRegs : ready.regs = initial.regs := undefinedRegs.trans stageRegs
  have selectionCall := selection_cached acc next ready normal (by rw [readyRegs]; exact cached)
  have exclusive := output_exclusive_ordinary acc next.memattrs (output_cached_ordinary acc initial.regs cached outputPolicy)
  obtain ⟨address, other, finishCall, _, _, addressAttrs, _, _, _, _, _, _, _⟩ :=
    output_finish_fields_total va acc params slot descriptor fault next oa next.memattrs ready (space.trans nonsecure) normal exclusive
  refine ⟨address, other, ?_, by rw [addressAttrs]; rfl, by rw [addressAttrs]; rfl⟩
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

#print axioms native_translate_suffix_cached
end ArmCertWalk
