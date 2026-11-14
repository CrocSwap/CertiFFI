import ArmCertWalk.TableUpdateTotal
import ArmCertWalk.TTWAccKind

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

/-- `TableUpdateEvents` plus: the actual swap base is a TTW descriptor. -/
def TableUpdateEventsTTW (params : S1TTWParams) (descriptor : BitVec 64)
    (acc : AccessDescriptor) (walkaddr : AddressDescriptor) (before after : State) : Prop :=
  if S1TableUpdate.word params descriptor = descriptor then after.events = before.events
  else ∃ base : AccessDescriptor, base.acctype = .AccessType_TTW ∧
    after.events = (before.events.push (swapReadEvent (S1AccDescFrame.updated acc base) walkaddr)).push
      (swapWriteEvent params.ee (S1TableUpdate.word params descriptor) (S1AccDescFrame.updated acc base) walkaddr)

/-- Internal source-callee composition. Its certificate is constructed by
`table_prefix_total`; the outer public walk entry requires current data only. -/
theorem table_action_history_ttw_total (params : S1TTWParams) (config : PhysicalConfig)
    (controls : S1LogicalReference.Controls) (footprint : Footprint)
    (level : Nat) (va : BitVec 64) (acc : AccessDescriptor)
    (walkaddr : AddressDescriptor) (ti : TranslationInfo) (s2 aligned : Bool)
    (descriptor : BitVec 64) (fault : FaultRecord) (a64 : Bool) (s2fault : FaultRecord)
    (current : TTWState) (initial : State)
    (c : TablePrefixCertificate params config controls current level descriptor va s2 initial)
    (d128 : params.d128 = 0#1) (tg : params.tgx = .TGx_4KB)
    (noFault : fault.statuscode = .Fault_None)
    (el : initial.regs.PSTATE.EL = 0#2 ∨ initial.regs.PSTATE.EL = 1#2)
    (noRME : initial.regs.FeatureImpl[232] = false)
    (aarch64 : initial.regs.PSTATE.nRW = 0#1)
    (el3A64 : initial.regs.FeatureImpl[7] = true)
    (noEL3A32 : initial.regs.FeatureImpl[3] = false)
    (ram : S2TableRAM.OrdinaryRAM walkaddr.paddress.address)
    (covered : walkaddr.paddress.address.toNat ∈ footprint.slots)
    (alignment : walkaddr.paddress.address.toNat % 8 = 0)
    (present : S1ByteMemory.DescAt initial.mem walkaddr.paddress.address.toNat
      (S2Endian.encode params.ee descriptor)) :
    ∃ other,
      S1WalkTable.action params va acc walkaddr ti s2 aligned descriptor fault a64 s2fault current initial =
        .ok (.ok (aligned, c.address, S1TableUpdate.word params descriptor,
          .DescriptorType_Table, fault, S1TableUpdate.word params descriptor, a64, s2fault, 0#2, c.next)) other ∧
      other.regs = initial.regs ∧
      StoreHistory params footprint initial.mem (tableOperations params walkaddr.paddress.address.toNat descriptor) other.mem ∧
      TableUpdateEventsTTW params descriptor acc walkaddr initial other := by
  have entryCall := c.entryCall
  have rangeCall := c.rangeCall
  simp only [d128, tg] at entryCall rangeCall
  have noneNe : ((.Fault_None : Fault) != .Fault_None) = false := by decide
  by_cases same : S1TableUpdate.word params descriptor = descriptor
  · refine ⟨c.state, ?_, c.registers, ?_, ?_⟩
    · simp [S1WalkTable.action, ← S1TableUpdate.word_def, same, Bind.bind, Pure.pure, Functor.map,
        ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.lift,
        EStateM.bind, EStateM.map, EStateM.pure, liftM, MonadLiftT.monadLift,
        MonadLift.monadLift, c.nextCall, entryCall, rangeCall]
    · simpa only [tableOperations, same, ↓reduceIte, c.memory] using
        (StoreHistory.nil initial.mem : StoreHistory params footprint initial.mem [] initial.mem)
    · simpa only [TableUpdateEventsTTW, same, ↓reduceIte] using c.events
  · let k := c.state.choiceOcc.getD 1607 0
    let afterLabel : State := {c.state with choiceOcc := c.state.choiceOcc.insert 1607 (k + 1)}
    have labelCall : occLabel 1607 c.state = .ok (.occ 1607 k) afterLabel := by rfl
    obtain ⟨unused, first, undefinedCall, undefinedRegs, undefinedMem, undefinedEvents⟩ :=
      S1Unknowns.undefined_address_total (.occ 1607 k) afterLabel
    have firstRegs : first.regs = initial.regs := undefinedRegs.trans c.registers
    obtain ⟨base, second, accessCall, accessRegs, accessMem, accessEvents⟩ :=
      S1AccDescFrame.update_total acc first (by simpa only [firstRegs] using el)
        (by simpa only [firstRegs] using noRME) (by simpa only [firstRegs] using aarch64)
        (by simpa only [firstRegs] using el3A64) (by simpa only [firstRegs] using noEL3A32)
    have secondRegs : second.regs = initial.regs := accessRegs.trans firstRegs
    have secondMem : second.mem = initial.mem := accessMem.trans (undefinedMem.trans c.memory)
    have secondEvents : second.events = initial.events := accessEvents.trans (undefinedEvents.trans c.events)
    obtain ⟨other, swapCall, swapRegs, stored, swapEvents⟩ :=
      swap_store_step_events params footprint (tableOperation params walkaddr.paddress.address.toNat descriptor)
        fault (S1AccDescFrame.updated acc base) walkaddr ti second
        (by simpa only [secondRegs] using noRME) ram rfl covered alignment
        (by simpa only [tableOperation, secondMem] using present) (table_word_allowed params descriptor)
    refine ⟨other, ?_, swapRegs.trans secondRegs, ?_, ?_⟩
    · simp only [tableOperation] at swapCall
      simp [S1WalkTable.action, ← S1TableUpdate.word_def, same, Bind.bind, Pure.pure, Functor.map,
        ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.lift,
        EStateM.bind, EStateM.map, EStateM.pure, liftM, MonadLiftT.monadLift,
        MonadLift.monadLift, c.nextCall, entryCall, rangeCall, labelCall, undefinedCall,
        accessCall, swapCall, noFault, noneNe]
    · have history : StoreHistory params footprint second.mem
          [tableOperation params walkaddr.paddress.address.toNat descriptor] other.mem :=
        .cons stored (.nil other.mem)
      simpa only [tableOperations, same, ↓reduceIte, secondMem] using history
    · simp only [TableUpdateEventsTTW, same, ↓reduceIte]
      exact ⟨base, update_base_ttw acc base first second (by simpa only [firstRegs] using el)
        (by simpa only [firstRegs] using noRME) (by simpa only [firstRegs] using aarch64)
        (by simpa only [firstRegs] using el3A64) (by simpa only [firstRegs] using noEL3A32) accessCall,
        by simpa only [tableOperation, secondEvents] using swapEvents⟩

#print axioms table_action_history_ttw_total
end ArmCertWalk
