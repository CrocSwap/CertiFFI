import ArmCertWalk.DescriptorFetchEvents
import ArmCertWalk.OuterPrefixTotal
import ArmCertWalk.TTWAccKind
import Walk.S1OuterSplit

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

theorem outer_prefix_ttw_total (params : S1TTWParams) (va : BitVec 64) (acc : AccessDescriptor)
    (startlevel : Int) (aligned : Bool) (descaddr : FullAddress) (oldDescriptor : BitVec 64)
    (typ : DescriptorType) (fault : FaultRecord) (a64 s2 : Bool) (skl : BitVec 2)
    (walkaddr : AddressDescriptor) (current : TTWState) (data : BitVec 64) (initial : State)
    (noFault : fault.statuscode = .Fault_None)
    (el : initial.regs.PSTATE.EL = 0#2 ∨ initial.regs.PSTATE.EL = 1#2)
    (noRME : initial.regs.FeatureImpl[232] = false)
    (aarch64 : initial.regs.PSTATE.nRW = 0#1)
    (el3A64 : initial.regs.FeatureImpl[7] = true)
    (noEL3A32 : initial.regs.FeatureImpl[3] = false)
    (ram : S2TableRAM.OrdinaryRAM descaddr.address)
    (present : S2ByteMemory.DescAt initial.mem descaddr.address.toNat data) :
    ∃ (out : S1OuterPrefix.Input) (base : AccessDescriptor) (other : State),
      base.acctype = .AccessType_TTW ∧
      S1OuterPrefix.action params va .Regime_EL20 acc startlevel
        (aligned, descaddr, oldDescriptor, typ, fault, a64, s2, skl, walkaddr, current) initial =
        .ok (.ok out) other ∧
      out.descriptor = S2FetchFrame.decoded params.ee data ∧
      out.fault = {fault with level := current.level} ∧
      out.walkaddr = {walkaddr with paddress := descaddr} ∧
      out.aligned = aligned ∧ out.a64 = a64 ∧ out.s2fs1mro = s2 ∧
      other.regs = initial.regs ∧ other.mem = initial.mem ∧
      other.events = initial.events.push (descriptorReadEvent
        (S1ReadAccDesc.value (current.level == startlevel) (AArch64_GetVARange va) acc base)
        {walkaddr with paddress := descaddr}
        (S1OuterSplit.info params .Regime_EL20 current {walkaddr with paddress := descaddr})) := by
  obtain ⟨base, first, accessCall, accessRegs, accessMem, accessEvents⟩ :=
    S1ReadAccDesc.total (current.level == startlevel) (AArch64_GetVARange va) acc initial
      el noRME aarch64 el3A64 noEL3A32
  let k1 := first.choiceOcc.getD 1603 0
  let u1 : State := {first with choiceOcc := first.choiceOcc.insert 1603 (k1 + 1)}
  have label1 : occLabel 1603 first = .ok (.occ 1603 k1) u1 := rfl
  obtain ⟨s2fault, second, faultCall, faultRegs, faultMem, faultEvents⟩ :=
    S1UnknownFault.total (.occ 1603 k1) u1
  let k2 := second.choiceOcc.getD 1604 0
  let u2 : State := {second with choiceOcc := second.choiceOcc.insert 1604 (k2 + 1)}
  have label2 : occLabel 1604 second = .ok (.occ 1604 k2) u2 := rfl
  obtain ⟨unused, third, undefinedCall, undefinedRegs, undefinedMem, undefinedEvents⟩ :=
    S1Unknowns.undefined_address_total (.occ 1604 k2) u2
  have thirdRegs : third.regs = initial.regs := undefinedRegs.trans (faultRegs.trans accessRegs)
  have thirdMem : third.mem = initial.mem := undefinedMem.trans (faultMem.trans accessMem)
  have thirdEvents : third.events = initial.events := undefinedEvents.trans (faultEvents.trans accessEvents)
  obtain ⟨fourth, fetchCall, fetchRegs, fetchMem, fetchEvents⟩ :=
    descriptor_fetch_total params.ee {fault with level := current.level} data
      (S1ReadAccDesc.value (current.level == startlevel) (AArch64_GetVARange va) acc base)
      {walkaddr with paddress := descaddr}
      (S1OuterSplit.info params .Regime_EL20 current {walkaddr with paddress := descaddr}) third
      (by simpa only [thirdRegs] using noRME) ram (by simpa only [thirdMem] using present)
  let k3 := fourth.choiceOcc.getD 1605 0
  let other : State := {fourth with choiceOcc := fourth.choiceOcc.insert 1605 (k3 + 1)}
  have label3 : occLabel 1605 fourth = .ok (.occ 1605 k3) other := rfl
  obtain ⟨newd, bitsCall⟩ := S1Unknowns.bits_at_total 64 (.occ 1605 k3) other
  have host : ((.Regime_EL20 : Regime) == .Regime_EL10) = false := by decide
  simp only [S1OuterSplit.info, noFault] at fetchCall
  have noneNe : ((.Fault_None : Fault) != .Fault_None) = false := by decide
  refine ⟨⟨aligned, S2FetchFrame.decoded params.ee data, {fault with level := current.level},
    a64, s2fault, s2, newd, {walkaddr with paddress := descaddr}⟩, base, other,
    read_base_ttw _ _ acc base initial first el noRME aarch64 el3A64 noEL3A32 accessCall, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl, fetchRegs.trans thirdRegs, fetchMem.trans thirdMem, ?_⟩
  · simp [S1OuterPrefix.action, S1DescriptorRead.action, S1OuterSplit.info,
      Bind.bind, Pure.pure, Functor.map, ExceptT.bind, ExceptT.bindCont,
      ExceptT.pure, ExceptT.mk, ExceptT.lift, ExceptT.map, EStateM.bind, EStateM.map, EStateM.pure,
      liftM, MonadLiftT.monadLift, MonadLift.monadLift, accessCall, label1, faultCall,
      label2, undefinedCall, host, fetchCall, label3, bitsCall, noFault, noneNe,
      Sail.Int.toNatChecked, Sail.BitVec.castWidth]
  · simpa only [thirdEvents] using fetchEvents

#print axioms outer_prefix_ttw_total
end ArmCertWalk
