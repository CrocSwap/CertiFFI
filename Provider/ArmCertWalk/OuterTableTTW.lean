import ArmCertWalk.OuterTableTotal
import ArmCertWalk.OuterPrefixTTW
import ArmCertWalk.TableLoopTTW

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

theorem outer_table_ttw_total (params : S1TTWParams) (config : PhysicalConfig)
    (controls : S1LogicalReference.Controls) (footprint : Footprint)
    (va : BitVec 64) (acc : AccessDescriptor) (startlevel : Int) (aligned : Bool)
    (descaddr : FullAddress) (oldDescriptor : BitVec 64) (typ : DescriptorType)
    (fault : FaultRecord) (a64 s2 : Bool) (skl : BitVec 2) (walkaddr : AddressDescriptor)
    (current : TTWState) (level : Nat) (descriptor : BitVec 64) (initial : State)
    (d128 : params.d128 = 0#1) (ds : params.ds = 0#1) (tg : params.tgx = .TGx_4KB)
    (ips : params.ps = config.ips) (physical : PhysicalAt config initial)
    (nonsecure : current.baseaddress.paspace = .PAS_NonSecure)
    (currentLevel : current.level = (level : Int)) (valid : level < 3)
    (regime : controls.regime = .el20)
    (hpd : controls.hpd = (params.hpd == 1#1)) (pie : controls.pie = (params.pie == 1#1))
    (bound : S1LogicalReference.entryAddress ((S1LogicalReference.pageBase descriptor).setWidth 48)
      va (level + 1) 9 < 2 ^ (effectiveBits config).toNat)
    (table : S1DecodeFacts.classify descriptor current.level = .DescriptorType_Table)
    (noFault : fault.statuscode = .Fault_None)
    (el : initial.regs.PSTATE.EL = 0#2 ∨ initial.regs.PSTATE.EL = 1#2)
    (noRME : initial.regs.FeatureImpl[232] = false)
    (aarch64 : initial.regs.PSTATE.nRW = 0#1)
    (el3A64 : initial.regs.FeatureImpl[7] = true)
    (noEL3A32 : initial.regs.FeatureImpl[3] = false)
    (ram : S2TableRAM.OrdinaryRAM descaddr.address)
    (covered : descaddr.address.toNat ∈ footprint.slots) (alignment : descaddr.address.toNat % 8 = 0)
    (present : S1ByteMemory.DescAt initial.mem descaddr.address.toNat (S2Endian.encode params.ee descriptor)) :
    ∃ (next : TTWState) (address : FullAddress) (readBase : AccessDescriptor) (other : State),
      readBase.acctype = .AccessType_TTW ∧
      S1WalkSource.named.body0 params va .Regime_EL20 acc 64 startlevel
        (aligned, descaddr, oldDescriptor, typ, fault, a64, s2, skl, walkaddr, current) initial =
        .ok (.ok (aligned, address, S1TableUpdate.word params descriptor, .DescriptorType_Table,
          {fault with level := current.level}, a64, s2, 0#2, {walkaddr with paddress := descaddr}, next)) other ∧
      NextTableMeaning params current descriptor next ∧
      next.baseaddress.address = S1LogicalReference.pageBase descriptor ∧
      nativeTablePermissionProjection next.permissions =
        S1LogicalReference.tablePermissions controls (nativeTablePermissionProjection current.permissions) descriptor ∧
      address.paspace = .PAS_NonSecure ∧ address.address.toNat = S1LogicalReference.entryAddress
        ((S1LogicalReference.pageBase descriptor).setWidth 48) va (level + 1) 9 ∧
      other.regs = initial.regs ∧
      StoreHistory params footprint initial.mem (tableOperations params descaddr.address.toNat descriptor) other.mem ∧
      (let readEvent := descriptorReadEvent
        (S1ReadAccDesc.value (current.level == startlevel) (AArch64_GetVARange va) acc readBase)
        {walkaddr with paddress := descaddr}
        (S1OuterSplit.info params .Regime_EL20 current {walkaddr with paddress := descaddr})
       if S1TableUpdate.word params descriptor = descriptor then other.events = initial.events.push readEvent
       else ∃ updateBase : AccessDescriptor, updateBase.acctype = .AccessType_TTW ∧
         other.events = ((initial.events.push readEvent).push
           (swapReadEvent (S1AccDescFrame.updated acc updateBase) {walkaddr with paddress := descaddr})).push
           (swapWriteEvent params.ee (S1TableUpdate.word params descriptor)
             (S1AccDescFrame.updated acc updateBase) {walkaddr with paddress := descaddr})) := by
  obtain ⟨out, readBase, first, readTTW, prefixCall, descEq, faultEq, addressEq, alignedEq, a64Eq, s2Eq,
    prefixRegs, prefixMem, prefixEvents⟩ :=
    outer_prefix_ttw_total params va acc startlevel aligned descaddr oldDescriptor typ fault a64 s2 skl walkaddr current
      (S2Endian.encode params.ee descriptor) initial noFault el noRME aarch64 el3A64 noEL3A32 ram present
  rw [fetch_decoded_encode] at descEq
  obtain ⟨c, other, tableCall, registers, history, events⟩ :=
    table_source_loop_history_ttw_total params config controls footprint level va acc
      {walkaddr with paddress := descaddr}
      (S1OuterSplit.info params .Regime_EL20 current {walkaddr with paddress := descaddr}) s2 aligned
      descaddr descriptor typ {fault with level := current.level} out.newd a64 out.s2fault skl current first
      d128 ds tg ips (physical.of_regs prefixRegs) nonsecure currentLevel valid regime hpd pie bound table noFault
      (by simpa only [prefixRegs] using el) (by simpa only [prefixRegs] using noRME)
      (by simpa only [prefixRegs] using aarch64) (by simpa only [prefixRegs] using el3A64)
      (by simpa only [prefixRegs] using noEL3A32) ram covered alignment
      (by simpa only [prefixMem] using present)
  refine ⟨c.next, c.address, readBase, other, readTTW, ?_, c.nextMeaning, c.nextBase, c.nextPermissions,
    c.addressSpace, c.addressSlot, registers.trans prefixRegs, ?_, ?_⟩
  · rw [S1OuterSplit.equation]
    simp [Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure, Pure.pure,
      EStateM.bind, EStateM.pure, prefixCall, S1OuterSplit.resume, descEq, faultEq, addressEq,
      alignedEq, a64Eq, s2Eq, tableCall]
  · simpa only [prefixMem] using history
  · simpa only [TableUpdateEventsTTW, prefixEvents] using events

#print axioms outer_table_ttw_total
end ArmCertWalk
