import ArmCertWalk.OuterLeafTotal
import ArmCertWalk.OuterPrefixTTW

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

theorem outer_leaf_ttw_total (config : AttributeConfig) (controls : S1LogicalReference.Controls)
    (params : S1TTWParams) (va : BitVec 64) (acc : AccessDescriptor)
    (startlevel : Int) (aligned : Bool) (descaddr : FullAddress) (oldDescriptor : BitVec 64)
    (typ : DescriptorType) (fault : FaultRecord) (a64 s2 : Bool) (skl : BitVec 2)
    (walkaddr : AddressDescriptor) (current : TTWState) (level : Nat)
    (descriptor : BitVec 64) (initial : State)
    (d128 : params.d128 = 0#1) (ds : params.ds = 0#1) (tg : params.tgx = .TGx_4KB)
    (aie : params.aie = 0#1) (pnch : params.pnch = 0#1)
    (nonsecure : current.baseaddress.paspace = .PAS_NonSecure)
    (ss : acc.ss = .SS_NonSecure) (currentLevel : current.level = (level : Int))
    (leaf : S1DecodeFacts.classify descriptor current.level = .DescriptorType_Leaf)
    (activeAttrs : ActiveAttributesAt config params initial)
    (admissible : AttributeAdmissible config (selectedAttribute config descriptor))
    (binding : LeafPermissionControls params (outputOverlayEnabled initial.regs) controls)
    (noFault : fault.statuscode = .Fault_None)
    (el : initial.regs.PSTATE.EL = 0#2 ∨ initial.regs.PSTATE.EL = 1#2)
    (noRME : initial.regs.FeatureImpl[232] = false)
    (aarch64 : initial.regs.PSTATE.nRW = 0#1)
    (el3A64 : initial.regs.FeatureImpl[7] = true)
    (noEL3A32 : initial.regs.FeatureImpl[3] = false)
    (ram : S2TableRAM.OrdinaryRAM descaddr.address)
    (present : S1ByteMemory.DescAt initial.mem descaddr.address.toNat (S2Endian.encode params.ee descriptor)) :
    ∃ (next : TTWState) (base : AccessDescriptor) (other : State),
      base.acctype = .AccessType_TTW ∧
      S1WalkSource.named.body0 params va .Regime_EL20 acc 64 startlevel
        (aligned, descaddr, oldDescriptor, typ, fault, a64, s2, skl, walkaddr, current) initial =
        .ok (.ok (aligned, descaddr, descriptor, .DescriptorType_Leaf,
          {fault with level := current.level}, a64, s2, skl, {walkaddr with paddress := descaddr}, next)) other ∧
      LeafMeaning config controls params (outputOverlayEnabled initial.regs) current level descriptor next ∧
      other.regs = initial.regs ∧ other.mem = initial.mem ∧
      other.events = initial.events.push (descriptorReadEvent
        (S1ReadAccDesc.value (current.level == startlevel) (AArch64_GetVARange va) acc base)
        {walkaddr with paddress := descaddr}
        (S1OuterSplit.info params .Regime_EL20 current {walkaddr with paddress := descaddr})) := by
  obtain ⟨out, base, first, baseTTW, prefixCall, descEq, faultEq, addressEq, alignedEq, a64Eq, s2Eq,
    prefixRegs, prefixMem, prefixEvents⟩ :=
    outer_prefix_ttw_total params va acc startlevel aligned descaddr oldDescriptor typ fault a64 s2 skl walkaddr current
      (S2Endian.encode params.ee descriptor) initial noFault el noRME aarch64 el3A64 noEL3A32 ram present
  rw [fetch_decoded_encode] at descEq
  have leafBinding : LeafPermissionControls params (outputOverlayEnabled first.regs) controls := by
    rw [prefixRegs]; exact binding
  obtain ⟨next, other, leafCall, meaning, registers, memory, events⟩ :=
    leaf_source_loop_total config controls params va acc {walkaddr with paddress := descaddr}
      (S1OuterSplit.info params .Regime_EL20 current {walkaddr with paddress := descaddr}) s2 aligned
      descaddr descriptor typ {fault with level := current.level} out.newd a64 out.s2fault skl current level first
      d128 ds tg aie pnch nonsecure ss currentLevel leaf (activeAttrs.of_regs prefixRegs) admissible leafBinding
  refine ⟨next, base, other, baseTTW, ?_, ?_, registers.trans prefixRegs, memory.trans prefixMem,
    events.trans prefixEvents⟩
  · rw [S1OuterSplit.equation]
    simp [Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure, Pure.pure,
      EStateM.bind, EStateM.pure, prefixCall, S1OuterSplit.resume, descEq, faultEq, addressEq,
      alignedEq, a64Eq, s2Eq, leafCall]
  · simpa only [prefixRegs] using meaning

#print axioms outer_leaf_ttw_total
end ArmCertWalk
