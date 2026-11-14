import ArmCertWalk.TableLoopTotal
import ArmCertWalk.TableUpdateTTW

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

theorem table_source_loop_history_ttw_total (params : S1TTWParams) (config : PhysicalConfig)
    (controls : S1LogicalReference.Controls) (footprint : Footprint)
    (level : Nat) (va : BitVec 64) (acc : AccessDescriptor)
    (walkaddr : AddressDescriptor) (ti : TranslationInfo) (s2 aligned : Bool)
    (descaddr : FullAddress) (descriptor : BitVec 64) (oldType : DescriptorType)
    (fault : FaultRecord) (oldNew : BitVec 64) (a64 : Bool) (s2fault : FaultRecord)
    (skl : BitVec 2) (current : TTWState) (initial : State)
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
    (ram : S2TableRAM.OrdinaryRAM walkaddr.paddress.address)
    (covered : walkaddr.paddress.address.toNat ∈ footprint.slots)
    (alignment : walkaddr.paddress.address.toNat % 8 = 0)
    (present : S1ByteMemory.DescAt initial.mem walkaddr.paddress.address.toNat
      (S2Endian.encode params.ee descriptor)) :
    ∃ (c : TablePrefixCertificate params config controls current level descriptor va s2 initial) (other : State),
      S1WalkSource.named.loop1 params va .Regime_EL20 acc 64 descaddr oldType skl current
        walkaddr ti aligned descriptor fault a64 s2fault s2 oldNew initial =
        .ok (.ok (aligned, c.address, S1TableUpdate.word params descriptor,
          .DescriptorType_Table, fault, S1TableUpdate.word params descriptor, a64, s2fault, 0#2, c.next)) other ∧
      other.regs = initial.regs ∧
      StoreHistory params footprint initial.mem (tableOperations params walkaddr.paddress.address.toNat descriptor) other.mem ∧
      TableUpdateEventsTTW params descriptor acc walkaddr initial other := by
  obtain ⟨c⟩ := table_prefix_total params config controls current level descriptor va s2 initial
    d128 ds tg ips physical nonsecure currentLevel valid regime hpd pie bound
  obtain ⟨other, actionCall, registers, history, events⟩ :=
    table_action_history_ttw_total params config controls footprint level va acc walkaddr ti s2 aligned
      descriptor fault a64 s2fault current initial c d128 tg noFault el noRME aarch64 el3A64 noEL3A32
      ram covered alignment present
  have body : S1WalkSource.named.body1 params va .Regime_EL20 acc 64 walkaddr ti s2
      (aligned, descaddr, descriptor, oldType, fault, oldNew, a64, s2fault, skl, current) initial =
      .ok (.ok (aligned, c.address, S1TableUpdate.word params descriptor,
        .DescriptorType_Table, fault, S1TableUpdate.word params descriptor, a64, s2fault, 0#2, c.next)) other := by
    rw [S1WalkTable.equation params va acc walkaddr ti s2 aligned descaddr descriptor oldType
      fault oldNew a64 s2fault skl current initial d128 ds tg table]
    exact actionCall
  have trace : S2Loop.Trace S1WalkInvalid.stop
      (S1WalkSource.named.body1 params va .Regime_EL20 acc 64 walkaddr ti s2)
      1 (aligned, descaddr, descriptor, oldType, fault, oldNew, a64, s2fault, skl, current) initial
      (.ok (aligned, c.address, S1TableUpdate.word params descriptor,
        .DescriptorType_Table, fault, S1TableUpdate.word params descriptor, a64, s2fault, 0#2, c.next)) other :=
    .done body (by simp [S1WalkInvalid.stop])
  refine ⟨c, other, ?_, registers, history, events⟩
  simpa only [S1WalkSource.named.loop1, S1WalkInvalid.stop] using
    S2Loop.execute trace 1048576 (by decide)

#print axioms table_source_loop_history_ttw_total
end ArmCertWalk
