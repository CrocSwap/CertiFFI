import Walk.S1WalkTable
import Walk.S1TablePrefix
import Pilot.S1HardwareSwap
import Walk.S1AccDescFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
set_option pp.maxSteps 2500
namespace S1TableUpdate
abbrev State := S1WalkInvalid.State
def word (wp : S1TTWParams) (d : BitVec 64) : BitVec 64 :=
  if wp.haft = 1#1 then BitVec.update d 10 (Bit 1#1) else d
theorem word_def (wp : S1TTWParams) (d : BitVec 64) :
    word wp d = (if wp.haft = 1#1 then BitVec.update d 10 (Bit 1#1) else d) := rfl
def observe (wp : S1TTWParams) :=
  S1HardwareSwap.observe wp.ee (wp.pie == 1#1) (wp.ha == 1#1) (wp.hd == 1#1)
theorem hardware_word (wp : S1TTWParams) (d : BitVec 64) :
    S1Descriptor.hardwareUpdate (wp.haft == 1#1) false d = word wp d := by
  have hb : Bit (1#1) = 1#1 := by decide
  by_cases h : wp.haft = 1#1 <;>
    simp [S1Descriptor.hardwareUpdate, S1Descriptor.setAF, word, h, hb]

theorem action_total (wp : S1TTWParams) (va : BitVec 64) (acc : AccessDescriptor)
    (walkaddr : AddressDescriptor) (ti : TranslationInfo) (s2fs1mro aligned : Bool)
    (d : BitVec 64) (fault : FaultRecord) (a64 : Bool) (s2fault : FaultRecord)
    (current : TTWState) (s : State)
    (c : S1TablePrefix.Certificate wp current d va s2fs1mro s)
    (hRange : S1TablePrefix.outOfRange wp (S1TablePrefix.address c.next va) = false)
    (hFault : fault.statuscode = .Fault_None)
    (hEL : s.regs.PSTATE.EL = 0#2 ∨ s.regs.PSTATE.EL = 1#2)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false)
    (hRAM : S2TableRAM.OrdinaryRAM walkaddr.paddress.address)
    (hAlign : walkaddr.paddress.address.toNat % 8 = 0)
    (hOld : S1ByteMemory.DescAt s.mem walkaddr.paddress.address.toNat
      (S2Endian.encode wp.ee d)) :
    ∃ t : State,
      S1WalkTable.action wp va acc walkaddr ti s2fs1mro aligned d fault a64 s2fault current s =
        .ok (.ok (aligned, S1TablePrefix.address c.next va, word wp d,
          .DescriptorType_Table, fault, word wp d, a64, s2fault, 0#2, c.next)) t ∧
      t.regs = s.regs ∧ S1MemoryObservation.Equivalent (observe wp) s.mem t.mem := by
  have hNoFault : ((.Fault_None : Fault) != .Fault_None) = false := by decide
  by_cases hSame : word wp d = d
  · refine ⟨c.state, ?_, c.regs_eq, ?_⟩
    · simp [S1WalkTable.action, ← word_def, hSame, Bind.bind, Pure.pure, Functor.map,
        ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.lift,
        EStateM.bind, EStateM.map, EStateM.pure, liftM, MonadLiftT.monadLift,
        MonadLift.monadLift, c.next_eq, c.address_eq, c.range_eq, hRange]
    · rw [c.mem_eq]
      intro a ha v
      rfl
  · let k := c.state.choiceOcc.getD 1607 0
    let afterLabel : State := {c.state with choiceOcc := c.state.choiceOcc.insert 1607 (k + 1)}
    have hLabel : occLabel 1607 c.state = .ok (.occ 1607 k) afterLabel := by rfl
    rcases S1Unknowns.undefined_address_total (.occ 1607 k) afterLabel with
      ⟨unused, t1, hu, hr1, hm1, _⟩
    have hRegs1 : t1.regs = s.regs := hr1.trans c.regs_eq
    rcases S1AccDescFrame.update_total acc t1 (by simpa only [hRegs1] using hEL)
      (by simpa only [hRegs1] using hNoRME)
      (by simpa only [hRegs1] using hA64)
      (by simpa only [hRegs1] using hEL3A64)
      (by simpa only [hRegs1] using hNoEL3A32) with
      ⟨base, t2, hacc, hr2, hm2, _⟩
    have hRegs2 : t2.regs = s.regs := hr2.trans hRegs1
    have hMem2 : t2.mem = s.mem := hm2.trans (hm1.trans c.mem_eq)
    rcases S1HardwareSwap.complete wp.ee (wp.pie == 1#1) (wp.ha == 1#1) (wp.hd == 1#1)
      (wp.haft == 1#1) false fault d (S1AccDescFrame.updated acc base) walkaddr ti t2
      (by simpa only [hRegs2] using hNoRME) hRAM hAlign
      (by simpa only [hMem2] using hOld) (by simp) with
      ⟨t, hswap, hr3, hobs, _⟩
    rw [hardware_word] at hswap
    refine ⟨t, ?_, hr3.trans hRegs2, ?_⟩
    · simp [S1WalkTable.action, ← word_def, hSame, Bind.bind, Pure.pure, Functor.map,
        ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.lift,
        EStateM.bind, EStateM.map, EStateM.pure, liftM, MonadLiftT.monadLift,
        MonadLift.monadLift, c.next_eq, c.address_eq, c.range_eq, hRange,
        hLabel, hu, hacc, hswap, hFault, hNoFault]
    · simpa only [observe, hMem2] using hobs
#print axioms action_total

theorem source_loop_total (wp : S1TTWParams) (va : BitVec 64) (acc : AccessDescriptor)
    (walkaddr : AddressDescriptor) (ti : TranslationInfo) (s2fs1mro aligned : Bool)
    (descaddr : FullAddress) (d : BitVec 64) (oldType : DescriptorType)
    (fault : FaultRecord) (oldNew : BitVec 64) (a64 : Bool) (s2fault : FaultRecord)
    (skl : BitVec 2) (current : TTWState) (s : State)
    (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1) (hTG : wp.tgx = .TGx_4KB)
    (hTable : S1DecodeFacts.classify d current.level = .DescriptorType_Table)
    (c : S1TablePrefix.Certificate wp current d va s2fs1mro s)
    (hRange : S1TablePrefix.outOfRange wp (S1TablePrefix.address c.next va) = false)
    (hFault : fault.statuscode = .Fault_None)
    (hEL : s.regs.PSTATE.EL = 0#2 ∨ s.regs.PSTATE.EL = 1#2)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false)
    (hRAM : S2TableRAM.OrdinaryRAM walkaddr.paddress.address)
    (hAlign : walkaddr.paddress.address.toNat % 8 = 0)
    (hOld : S1ByteMemory.DescAt s.mem walkaddr.paddress.address.toNat
      (S2Endian.encode wp.ee d)) :
    ∃ t : State,
      S1WalkSource.named.loop1 wp va .Regime_EL20 acc 64 descaddr oldType skl current
        walkaddr ti aligned d fault a64 s2fault s2fs1mro oldNew s =
        .ok (.ok (aligned, S1TablePrefix.address c.next va, word wp d,
          .DescriptorType_Table, fault, word wp d, a64, s2fault, 0#2, c.next)) t ∧
      t.regs = s.regs ∧ S1MemoryObservation.Equivalent (observe wp) s.mem t.mem := by
  rcases action_total wp va acc walkaddr ti s2fs1mro aligned d fault a64 s2fault current s
    c hRange hFault hEL hNoRME hA64 hEL3A64 hNoEL3A32 hRAM hAlign hOld with
    ⟨t, ha, hregs, hobs⟩
  have hr : S1WalkSource.named.body1 wp va .Regime_EL20 acc 64 walkaddr ti s2fs1mro
      (aligned, descaddr, d, oldType, fault, oldNew, a64, s2fault, skl, current) s =
      .ok (.ok (aligned, S1TablePrefix.address c.next va, word wp d,
        .DescriptorType_Table, fault, word wp d, a64, s2fault, 0#2, c.next)) t := by
    rw [S1WalkTable.equation wp va acc walkaddr ti s2fs1mro aligned descaddr d oldType
      fault oldNew a64 s2fault skl current s hD128 hDS hTG hTable]
    exact ha
  have trace : S2Loop.Trace S1WalkInvalid.stop
      (S1WalkSource.named.body1 wp va .Regime_EL20 acc 64 walkaddr ti s2fs1mro)
      1 (aligned, descaddr, d, oldType, fault, oldNew, a64, s2fault, skl, current) s
      (.ok (aligned, S1TablePrefix.address c.next va, word wp d,
        .DescriptorType_Table, fault, word wp d, a64, s2fault, 0#2, c.next)) t :=
    .done hr (by simp [S1WalkInvalid.stop])
  refine ⟨t, ?_, hregs, hobs⟩
  simpa only [S1WalkSource.named.loop1, S1WalkInvalid.stop] using
    S2Loop.execute trace 1048576 (by decide)
#print axioms source_loop_total
end S1TableUpdate
