import ArmCertWalk.TranslateUpdateSource
import ArmCertWalk.LeafUpdateData
import ArmCertTranslateModel.SwapEvents

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

def leafOperation (params : S1TTWParams) (acc : AccessDescriptor) (slot : Nat) (descriptor : BitVec 64) : TableUpdate :=
  {slot := slot, role := .leaf, before := descriptor, after := leafUpdateWord params acc descriptor}

def leafOperations (params : S1TTWParams) (acc : AccessDescriptor) (slot : Nat) (descriptor : BitVec 64) : List TableUpdate :=
  if leafUpdateWord params acc descriptor = descriptor then [] else [leafOperation params acc slot descriptor]

def leafSwapMem (params : S1TTWParams) (acc : AccessDescriptor) (descriptor : BitVec 64) (old : BitVec 128) : BitVec 128 :=
  if leafUpdateWord params acc descriptor = descriptor then old else (leafUpdateWord params acc descriptor).setWidth 128

def LeafUpdateEvents (params : S1TTWParams) (acc : AccessDescriptor) (descriptor : BitVec 64)
    (slot : AddressDescriptor) (before after : State) : Prop :=
  if leafUpdateWord params acc descriptor = descriptor then after.events = before.events
  else ∃ base : AccessDescriptor,
    after.events = (before.events.push (swapReadEvent (S1AccDescFrame.updated acc base) slot)).push
      (swapWriteEvent params.ee (leafUpdateWord params acc descriptor) (S1AccDescFrame.updated acc base) slot)

theorem leaf_update_stop (params : S1TTWParams) (acc : AccessDescriptor) (descriptor : BitVec 64)
    (old : BitVec 128) :
    (((leafUpdateWord params acc descriptor).setWidth 128 == descriptor.setWidth 128) ||
      (leafSwapMem params acc descriptor old == (leafUpdateWord params acc descriptor).setWidth 128)) = true := by
  by_cases same : leafUpdateWord params acc descriptor = descriptor <;> simp [leafSwapMem, same]

/-- Actual conditional leaf descriptor swap. A changed word produces exactly
one source read/write pair and returns the updated descriptor; no-change keeps
all old scratch data. The loop stop is a conclusion, not a retry bound input. -/
theorem leaf_swap_total (params : S1TTWParams) (footprint : Footprint) (va : BitVec 64)
    (acc oldAccess : AccessDescriptor) (slot : AddressDescriptor) (descriptor : BitVec 64)
    (fault : FaultRecord) (memDescriptor : BitVec 128) (a64 s2 : Bool) (next : TTWState) (state : State)
    (d128 : params.d128 = 0#1)
    (el : state.regs.PSTATE.EL = 0#2 ∨ state.regs.PSTATE.EL = 1#2)
    (noRME : state.regs.FeatureImpl[232] = false) (aarch64 : state.regs.PSTATE.nRW = 0#1)
    (el3A64 : state.regs.FeatureImpl[7] = true) (noEL3A32 : state.regs.FeatureImpl[3] = false)
    (ram : S2TableRAM.OrdinaryRAM slot.paddress.address)
    (covered : slot.paddress.address.toNat ∈ footprint.slots) (alignment : slot.paddress.address.toNat % 8 = 0)
    (present : S1ByteMemory.DescAt state.mem slot.paddress.address.toNat (S2Endian.encode params.ee descriptor)) :
    ∃ accessOut other,
      TranslateUpdateSource.swapAction params va acc oldAccess slot (descriptor.setWidth 128)
        fault memDescriptor ((leafUpdateWord params acc descriptor).setWidth 128) a64 s2 next state =
        .ok (.ok (accessOut, fault, leafSwapMem params acc descriptor memDescriptor, a64, s2)) other ∧
      other.regs = state.regs ∧
      StoreHistory params footprint state.mem (leafOperations params acc slot.paddress.address.toNat descriptor) other.mem ∧
      LeafUpdateEvents params acc descriptor slot state other := by
  by_cases same : leafUpdateWord params acc descriptor = descriptor
  · refine ⟨oldAccess, state, ?_, rfl, ?_, ?_⟩
    · simp [TranslateUpdateSource.swapAction, same, leafSwapMem, Bind.bind, Pure.pure,
        ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure, EStateM.bind, EStateM.pure]
    · simpa only [leafOperations, same, ↓reduceIte] using
        (StoreHistory.nil state.mem : StoreHistory params footprint state.mem [] state.mem)
    · simp only [LeafUpdateEvents, same, ↓reduceIte]
  · have wideDifferent : (leafUpdateWord params acc descriptor).setWidth 128 ≠ descriptor.setWidth 128 := by
      intro equal; exact same (descriptor128_injective _ _ equal)
    let k := state.choiceOcc.getD 1619 0
    let afterLabel : State := {state with choiceOcc := state.choiceOcc.insert 1619 (k + 1)}
    have labelCall : occLabel 1619 state = .ok (.occ 1619 k) afterLabel := rfl
    obtain ⟨unused, first, undefinedCall, undefinedRegs, undefinedMem, undefinedEvents⟩ :=
      S1Unknowns.undefined_address_total (.occ 1619 k) afterLabel
    obtain ⟨base, second, accessCall, accessRegs, accessMem, accessEvents⟩ :=
      S1AccDescFrame.update_total acc first (by rw [undefinedRegs]; exact el)
        (by rw [undefinedRegs]; exact noRME) (by rw [undefinedRegs]; exact aarch64)
        (by rw [undefinedRegs]; exact el3A64) (by rw [undefinedRegs]; exact noEL3A32)
    have secondRegs : second.regs = state.regs := accessRegs.trans undefinedRegs
    have secondMem : second.mem = state.mem := accessMem.trans undefinedMem
    have secondEvents : second.events = state.events := accessEvents.trans undefinedEvents
    let info : TranslationInfo :=
      {regime := .Regime_EL20, vmid := none, asid := none, va := va, s1level := some next.level,
       s2info := none, s1params := some params, s2params := none, memattrs := next.memattrs}
    obtain ⟨other, swapCall, swapRegs, stored, swapEvents⟩ :=
      swap_store_step_events params footprint (leafOperation params acc slot.paddress.address.toNat descriptor)
        fault (S1AccDescFrame.updated acc base) slot info second
        (by rw [secondRegs]; exact noRME) ram rfl covered alignment
        (by simpa only [leafOperation, secondMem] using present) (leaf_update_allowed params acc descriptor)
    have otherRegime : ((.Regime_EL20 : Regime) == .Regime_EL10) = false := rfl
    have d128False : ((0#1 : BitVec 1) == 1#1) = false := rfl
    have wideResult := source_descriptor_128 memDescriptor (leafUpdateWord params acc descriptor)
    unfold sourceDescriptor128 at wideResult
    refine ⟨S1AccDescFrame.updated acc base, other, ?_, swapRegs.trans secondRegs, ?_, ?_⟩
    · simp only [leafOperation] at swapCall
      simp [TranslateUpdateSource.swapAction, wideDifferent, d128, d128False, otherRegime,
        descriptor128_low, wideResult, leafSwapMem, same, info, labelCall, undefinedCall,
        accessCall, swapCall, Bind.bind, Pure.pure, Functor.map, ExceptT.bind,
        ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.lift, EStateM.bind, EStateM.map,
        EStateM.pure, liftM, MonadLiftT.monadLift, MonadLift.monadLift]
    · have history : StoreHistory params footprint second.mem
          [leafOperation params acc slot.paddress.address.toNat descriptor] other.mem :=
        .cons stored (.nil other.mem)
      simpa only [leafOperations, same, ↓reduceIte, secondMem] using history
    · simp only [LeafUpdateEvents, same, ↓reduceIte]
      exact ⟨base, by simpa only [leafOperation, secondEvents] using swapEvents⟩

#print axioms leaf_update_stop
#print axioms leaf_swap_total
end ArmCertWalk
