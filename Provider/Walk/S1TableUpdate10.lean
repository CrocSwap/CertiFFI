import Walk.S1TableTranslate10
import Walk.S1EL10PermsCallees
import Walk.S1TablePrefix10
import Pilot.S1HardwareSwap
import Walk.S1AccDescFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
set_option pp.maxSteps 2500
namespace S1TableUpdate10
abbrev State := S1WalkInvalid.State
abbrev Return := S1WalkInvalid.Return
abbrev Vars := S1WalkInvalid.Vars
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

def tableAction (wp : S1TTWParams) (va : BitVec 64) (acc : AccessDescriptor)
    (walkaddr : AddressDescriptor) (ti : TranslationInfo) (s2fs1mro aligned : Bool)
    (d : BitVec 64) (fault : FaultRecord) (a64 : Bool) (s2fault : FaultRecord)
    (current : TTWState) : SailME Return Vars := do
  let next ← AArch64_S1NextWalkStateTable current s2fs1mro .Regime_EL10 wp d
  let addr ← AArch64_TTEntryAddress next.level 0#1 0#2 .TGx_4KB wp.txsz va next.baseaddress
  let outOfRange ← AArch64_OAOutOfRange addr.address 0#1 wp.ps .TGx_4KB
  let (fault, newd) ← if outOfRange then do
      S1WalkTable10.early {fault with statuscode := .Fault_AddressSize}
    else pure (fault, if wp.haft == 1#1 then BitVec.update d 10 (Bit 1#1) else d)
  let (aligned, observed, fault, a64, s2fault) ← if newd != d then do
      let _ ← undefined_AddressDescriptor (← occLabel 1607) ()
      let descaccess ← CreateAccDescTTEUpdate acc
      let enabled ← EL2Enabled ()
      let (aligned, descpaddr, a64, s2fault) ←
        S1TableTranslate10.action enabled aligned a64 fault s2fault walkaddr next.level descaccess
      let (fault, observed) ← AArch64_MemSwapTableDesc fault d newd wp.ee descaccess descpaddr ti
      if bne fault.statuscode .Fault_None then S1WalkTable10.early fault else pure ()
      pure (aligned, observed, fault, a64, s2fault)
    else pure (aligned, d, fault, a64, s2fault)
  pure (aligned, addr, observed, .DescriptorType_Table, fault, newd, a64, s2fault, 0#2, next)

theorem action_run (wp : S1TTWParams) (va : BitVec 64) (acc : AccessDescriptor)
    (walkaddr : AddressDescriptor) (ti : TranslationInfo) (s2fs1mro aligned : Bool)
    (d : BitVec 64) (fault : FaultRecord) (a64 : Bool) (s2fault : FaultRecord)
    (current : TTWState) :
    S1WalkTable10.action wp va acc walkaddr ti s2fs1mro aligned d fault a64 s2fault current =
      tableAction wp va acc walkaddr ti s2fs1mro aligned d fault a64 s2fault current := by
  simp [S1WalkTable10.action, tableAction, S1TableTranslate10.action,
    S1WalkTable.bind_ite, bind_assoc]

theorem action_total (wp : S1TTWParams) (va : BitVec 64) (acc : AccessDescriptor)
    (walkaddr : AddressDescriptor) (ti : TranslationInfo) (s2fs1mro aligned : Bool)
    (d : BitVec 64) (fault : FaultRecord) (a64 : Bool) (s2fault : FaultRecord)
    (current : TTWState) (s : State) (cfg : S2Interface.Config)
    (c : S1TablePrefix10.Certificate wp current d va s2fs1mro s)
    (hRange : S1TablePrefix10.outOfRange wp (S1TablePrefix10.address c.next va) = false)
    (hConfig : S2Interface.ConfigAt cfg s)
    (hVM : _get_HCR_EL2_Type_VM cfg.hcr = 0#1)
    (hDC : _get_HCR_EL2_Type_DC cfg.hcr = 0#1)
    (hSS : acc.ss = .SS_NonSecure)
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
    ∃ (alignedOut a64Out : Bool) (s2faultOut : FaultRecord) (t : State),
      S1WalkTable10.action wp va acc walkaddr ti s2fs1mro aligned d fault a64 s2fault current s =
        .ok (.ok (alignedOut, S1TablePrefix10.address c.next va, word wp d,
          .DescriptorType_Table, fault, word wp d, a64Out, s2faultOut, 0#2, c.next)) t ∧
      t.regs = s.regs ∧ S1MemoryObservation.Equivalent (observe wp) s.mem t.mem := by
  rw [action_run]
  have hNoFault : ((.Fault_None : Fault) != .Fault_None) = false := by decide
  by_cases hSame : word wp d = d
  · refine ⟨aligned, a64, s2fault, c.state, ?_, c.frame.1, ?_⟩
    · simp [tableAction, ← word_def, hSame, Bind.bind, Pure.pure, Functor.map,
        ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.lift,
        EStateM.bind, EStateM.map, EStateM.pure, liftM, MonadLiftT.monadLift,
        MonadLift.monadLift, c.next_eq, c.address_eq, c.range_eq, hRange]
    · rw [c.frame.2.1]
      intro a ha v
      rfl
  · let k := c.state.choiceOcc.getD 1607 0
    let afterLabel : State := {c.state with choiceOcc := c.state.choiceOcc.insert 1607 (k + 1)}
    have hLabel : occLabel 1607 c.state = .ok (.occ 1607 k) afterLabel := by rfl
    rcases S1Unknowns.undefined_address_total (.occ 1607 k) afterLabel with
      ⟨unused, t1, hu, hr1, hm1, _⟩
    have hRegs1 : t1.regs = s.regs := hr1.trans c.frame.1
    rcases S1AccDescFrame.update_total acc t1 (by simpa only [hRegs1] using hEL)
      (by simpa only [hRegs1] using hNoRME)
      (by simpa only [hRegs1] using hA64)
      (by simpa only [hRegs1] using hEL3A64)
      (by simpa only [hRegs1] using hNoEL3A32) with
      ⟨base, t2, hacc, hr2, hm2, _⟩
    have hRegs2 : t2.regs = s.regs := hr2.trans hRegs1
    have hMem2 : t2.mem = s.mem := hm2.trans (hm1.trans c.frame.2.1)
    rcases S1EL10PermsCallees.el2_normal t2 with ⟨enabled, t3, hel2, hr3, hm3, _⟩
    have hRegs3 : t3.regs = s.regs := hr3.trans hRegs2
    have hMem3 : t3.mem = s.mem := hm3.trans hMem2
    have hConfig3 : S2Interface.ConfigAt cfg t3 := by
      rcases hConfig with ⟨a, b, c, d, e, f, g, h⟩
      exact ⟨by simpa only [hRegs3] using a, by simpa only [hRegs3] using b,
        by simpa only [hRegs3] using c, by simpa only [hRegs3] using d,
        by simpa only [hRegs3] using e, by simpa only [hRegs3] using f,
        by simpa only [hRegs3] using g, by simpa only [hRegs3] using h⟩
    rcases S1TableTranslate10.total enabled aligned a64 fault s2fault walkaddr c.next.level
      (S1AccDescFrame.updated acc base) cfg t3 hConfig3 hVM hDC hSS with
      ⟨alignedOut, a64Out, s2faultOut, t4, htranslate, hr4, hm4, _⟩
    have hRegs4 : t4.regs = s.regs := hr4.trans hRegs3
    have hMem4 : t4.mem = s.mem := hm4.trans hMem3
    rcases S1HardwareSwap.complete wp.ee (wp.pie == 1#1) (wp.ha == 1#1) (wp.hd == 1#1)
      (wp.haft == 1#1) false fault d (S1AccDescFrame.updated acc base) walkaddr ti t4
      (by simpa only [hRegs4] using hNoRME) hRAM hAlign
      (by simpa only [hMem4] using hOld) (by simp) with
      ⟨t, hswap, hr5, hobs, _⟩
    rw [hardware_word] at hswap
    refine ⟨alignedOut, a64Out, s2faultOut, t, ?_, hr5.trans hRegs4, ?_⟩
    · simp [tableAction, ← word_def, hSame, Bind.bind, Pure.pure, Functor.map,
        ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.lift,
        EStateM.bind, EStateM.map, EStateM.pure, liftM, MonadLiftT.monadLift,
        MonadLift.monadLift, c.next_eq, c.address_eq, c.range_eq, hRange,
        hLabel, hu, hacc, hel2, htranslate, hswap, hFault, hNoFault]
    · simpa only [observe, hMem4] using hobs
#print axioms action_total

theorem source_loop_total (wp : S1TTWParams) (va : BitVec 64) (acc : AccessDescriptor)
    (walkaddr : AddressDescriptor) (ti : TranslationInfo) (s2fs1mro aligned : Bool)
    (descaddr : FullAddress) (d : BitVec 64) (oldType : DescriptorType)
    (fault : FaultRecord) (oldNew : BitVec 64) (a64 : Bool) (s2fault : FaultRecord)
    (skl : BitVec 2) (current : TTWState) (s : State) (cfg : S2Interface.Config)
    (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1) (hTG : wp.tgx = .TGx_4KB)
    (hTable : S1DecodeFacts.classify d current.level = .DescriptorType_Table)
    (c : S1TablePrefix10.Certificate wp current d va s2fs1mro s)
    (hRange : S1TablePrefix10.outOfRange wp (S1TablePrefix10.address c.next va) = false)
    (hConfig : S2Interface.ConfigAt cfg s)
    (hVM : _get_HCR_EL2_Type_VM cfg.hcr = 0#1)
    (hDC : _get_HCR_EL2_Type_DC cfg.hcr = 0#1)
    (hSS : acc.ss = .SS_NonSecure)
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
    ∃ (alignedOut a64Out : Bool) (s2faultOut : FaultRecord) (t : State),
      S1WalkSource.named.loop1 wp va .Regime_EL10 acc 64 descaddr oldType skl current
        walkaddr ti aligned d fault a64 s2fault s2fs1mro oldNew s =
        .ok (.ok (alignedOut, S1TablePrefix10.address c.next va, word wp d,
          .DescriptorType_Table, fault, word wp d, a64Out, s2faultOut, 0#2, c.next)) t ∧
      t.regs = s.regs ∧ S1MemoryObservation.Equivalent (observe wp) s.mem t.mem := by
  rcases action_total wp va acc walkaddr ti s2fs1mro aligned d fault a64 s2fault current s cfg
    c hRange hConfig hVM hDC hSS hFault hEL hNoRME hA64 hEL3A64 hNoEL3A32 hRAM hAlign hOld with
    ⟨alignedOut, a64Out, s2faultOut, t, ha, hregs, hobs⟩
  have hr : S1WalkSource.named.body1 wp va .Regime_EL10 acc 64 walkaddr ti s2fs1mro
      (aligned, descaddr, d, oldType, fault, oldNew, a64, s2fault, skl, current) s =
      .ok (.ok (alignedOut, S1TablePrefix10.address c.next va, word wp d,
        .DescriptorType_Table, fault, word wp d, a64Out, s2faultOut, 0#2, c.next)) t := by
    rw [S1WalkTable10.equation wp va acc walkaddr ti s2fs1mro aligned descaddr d oldType
      fault oldNew a64 s2fault skl current s hD128 hDS hTG hTable]
    exact ha
  have trace : S2Loop.Trace S1WalkInvalid.stop
      (S1WalkSource.named.body1 wp va .Regime_EL10 acc 64 walkaddr ti s2fs1mro)
      1 (aligned, descaddr, d, oldType, fault, oldNew, a64, s2fault, skl, current) s
      (.ok (alignedOut, S1TablePrefix10.address c.next va, word wp d,
        .DescriptorType_Table, fault, word wp d, a64Out, s2faultOut, 0#2, c.next)) t :=
    .done hr (by simp [S1WalkInvalid.stop])
  refine ⟨alignedOut, a64Out, s2faultOut, t, ?_, hregs, hobs⟩
  simpa only [S1WalkSource.named.loop1, S1WalkInvalid.stop] using
    S2Loop.execute trace 1048576 (by decide)
#print axioms source_loop_total
end S1TableUpdate10

