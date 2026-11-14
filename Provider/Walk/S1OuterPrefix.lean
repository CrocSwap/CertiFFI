import Walk.S1OuterBody
import Walk.S1EL10PermsCallees
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1OuterPrefix
abbrev State := S1OuterBody.State
abbrev Return := S1OuterBody.Return
abbrev Vars := S1OuterBody.Vars
structure Input where
  aligned : Bool
  descriptor : BitVec 64
  fault : FaultRecord
  a64 : Bool
  s2fault : FaultRecord
  s2fs1mro : Bool
  newd : BitVec 64
  walkaddr : AddressDescriptor
def action (wp : S1TTWParams) (va : BitVec 64) (regime : Regime)
    (acc : AccessDescriptor) (startlevel : Int) : Vars → SailME Return Input
  | (aligned, descaddr, d, typ, fault, a64, s2fs1mro, skl, walkaddr, current) => do
    let fault := {fault with level := current.level}
    let walkaddr := {walkaddr with paddress := descaddr}
    let walkacc ← CreateAccDescS1TTW (current.level == startlevel) (AArch64_GetVARange va) acc
    let s2fault ← undefined_FaultRecord (← occLabel 1603) ()
    let _ ← undefined_AddressDescriptor (← occLabel 1604) ()
    let enabled ← if regime == .Regime_EL10 then EL2Enabled () else pure false
    let (aligned, d, fault, a64, s2fault, s2fs1mro) ←
      S1DescriptorRead.action enabled aligned a64 s2fs1mro wp.ee fault s2fault
        walkaddr current.level walkacc {
          regime := regime
          vmid := none
          asid := none
          va := walkaddr.vaddress
          s1level := some current.level
          s2info := none
          s1params := some wp
          s2params := none
          memattrs := walkaddr.memattrs}
    if bne fault.statuscode .Fault_None then S1WalkTable10.early fault else pure ()
    let newd ← (Sail.BitVec.castWidth (m := 64) <$>
      undefined_bitvector_at (← occLabel 1605) (Sail.Int.toNatChecked (64 : Int)))
    pure ⟨aligned, d, fault, a64, s2fault, s2fs1mro, newd, walkaddr⟩

theorem total (wp : S1TTWParams) (va : BitVec 64) (regime : Regime)
    (acc : AccessDescriptor) (startlevel : Int)
    (aligned : Bool) (descaddr : FullAddress) (d : BitVec 64) (typ : DescriptorType)
    (fault : FaultRecord) (a64 s2fs1mro : Bool) (skl : BitVec 2)
    (walkaddr : AddressDescriptor) (current : TTWState) (cfg : S2Interface.Config)
    (data : BitVec 64) (s : State)
    (hFault : fault.statuscode = .Fault_None)
    (hConfig : S2Interface.ConfigAt cfg s)
    (hVM : _get_HCR_EL2_Type_VM cfg.hcr = 0#1)
    (hDC : _get_HCR_EL2_Type_DC cfg.hcr = 0#1)
    (hSS : acc.ss = .SS_NonSecure)
    (hEL : s.regs.PSTATE.EL = 0#2 ∨ s.regs.PSTATE.EL = 1#2)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false)
    (hRAM : S2TableRAM.OrdinaryRAM descaddr.address)
    (hOld : S2ByteMemory.DescAt s.mem descaddr.address.toNat data) :
    ∃ (out : Input) (t : State),
      action wp va regime acc startlevel
        (aligned, descaddr, d, typ, fault, a64, s2fs1mro, skl, walkaddr, current) s =
        .ok (.ok out) t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧
      out.descriptor = S2FetchFrame.decoded wp.ee data ∧
      out.fault = {fault with level := current.level} ∧
      out.walkaddr = {walkaddr with paddress := descaddr} := by
  rcases S1ReadAccDesc.total (current.level == startlevel) (AArch64_GetVARange va) acc s
    hEL hNoRME hA64 hEL3A64 hNoEL3A32 with ⟨base, t1, hacc, hr1, hm1, _⟩
  let k1 := t1.choiceOcc.getD 1603 0
  let u1 : State := {t1 with choiceOcc := t1.choiceOcc.insert 1603 (k1 + 1)}
  have hl1 : occLabel 1603 t1 = .ok (.occ 1603 k1) u1 := rfl
  rcases S1UnknownFault.total (.occ 1603 k1) u1 with ⟨s2fault, t2, hf, hr2, hm2, _⟩
  let k2 := t2.choiceOcc.getD 1604 0
  let u2 : State := {t2 with choiceOcc := t2.choiceOcc.insert 1604 (k2 + 1)}
  have hl2 : occLabel 1604 t2 = .ok (.occ 1604 k2) u2 := rfl
  rcases S1Unknowns.undefined_address_total (.occ 1604 k2) u2 with
    ⟨unused, t3, hu, hr3, hm3, _⟩
  have hRegs3 : t3.regs = s.regs := hr3.trans (hr2.trans hr1)
  have hMem3 : t3.mem = s.mem := hm3.trans (hm2.trans hm1)
  have hn : S1Normality.Normal (if regime == .Regime_EL10 then EL2Enabled () else pure false) := by
    split
    · exact S1EL10PermsCallees.el2_normal
    · exact S1Normality.pure_normal false
  rcases hn t3 with ⟨enabled, t4, hel2, hr4, hm4, _⟩
  have hRegs4 : t4.regs = s.regs := hr4.trans hRegs3
  have hMem4 : t4.mem = s.mem := hm4.trans hMem3
  have hc4 : S2Interface.ConfigAt cfg t4 := by
    rcases hConfig with ⟨a, b, c, d, e, f, g, h⟩
    exact ⟨by simpa only [hRegs4] using a, by simpa only [hRegs4] using b,
      by simpa only [hRegs4] using c, by simpa only [hRegs4] using d,
      by simpa only [hRegs4] using e, by simpa only [hRegs4] using f,
      by simpa only [hRegs4] using g, by simpa only [hRegs4] using h⟩
  rcases S1DescriptorRead.total enabled aligned a64 s2fs1mro wp.ee
    {fault with level := current.level} s2fault {walkaddr with paddress := descaddr}
    current.level (S1ReadAccDesc.value (current.level == startlevel) (AArch64_GetVARange va) acc base)
    {regime := regime, vmid := none, asid := none, va := walkaddr.vaddress,
      s1level := some current.level, s2info := none, s1params := some wp,
      s2params := none, memattrs := walkaddr.memattrs}
    data cfg t4 hc4 hVM hDC hSS (by simpa only [hRegs4] using hNoRME) hRAM
    (by simpa only [hMem4] using hOld) with ⟨ao, a64o, s2fo, t5, hread, hr5, hm5⟩
  let k3 := t5.choiceOcc.getD 1605 0
  let t6 : State := {t5 with choiceOcc := t5.choiceOcc.insert 1605 (k3 + 1)}
  have hl3 : occLabel 1605 t5 = .ok (.occ 1605 k3) t6 := rfl
  rcases S1Unknowns.bits_at_total 64 (.occ 1605 k3) t6 with ⟨newd, hb⟩
  have hNoFault : ((.Fault_None : Fault) != .Fault_None) = false := by decide
  refine ⟨⟨ao, S2FetchFrame.decoded wp.ee data, {fault with level := current.level},
    a64o, s2fo, if enabled then walkaddr.s2fs1mro else s2fs1mro, newd,
    {walkaddr with paddress := descaddr}⟩, t6, ?_,
    hr5.trans hRegs4, hm5.trans hMem4, rfl, rfl, rfl⟩
  by_cases hReg : (regime == .Regime_EL10) = true
  · simp only [hReg, ↓reduceIte] at hel2
    simp [action, hReg, Bind.bind, Pure.pure, Functor.map, ExceptT.bind, ExceptT.bindCont,
      ExceptT.pure, ExceptT.mk, ExceptT.lift, ExceptT.map, EStateM.bind, EStateM.map, EStateM.pure,
      liftM, MonadLiftT.monadLift, MonadLift.monadLift, hacc, hl1, hf, hl2, hu, hel2,
      hread, hl3, hb]
    simp [hFault, hNoFault, Sail.Int.toNatChecked, Sail.BitVec.castWidth, Bind.bind, Pure.pure, Functor.map, ExceptT.bind, ExceptT.bindCont,
      ExceptT.pure, ExceptT.mk, ExceptT.lift, ExceptT.map, EStateM.bind, EStateM.map, EStateM.pure,
      liftM, MonadLiftT.monadLift, MonadLift.monadLift, hl3, hb]
  · simp only [hReg, ↓reduceIte, Pure.pure, EStateM.pure] at hel2
    cases hel2
    simp [action, hReg, Bind.bind, Pure.pure, Functor.map, ExceptT.bind, ExceptT.bindCont,
      ExceptT.pure, ExceptT.mk, ExceptT.lift, ExceptT.map, EStateM.bind, EStateM.map, EStateM.pure,
      liftM, MonadLiftT.monadLift, MonadLift.monadLift, hacc, hl1, hf, hl2, hu,
      hread, hl3, hb]
    simp [hFault, hNoFault, Sail.Int.toNatChecked, Sail.BitVec.castWidth, Bind.bind, Pure.pure, Functor.map, ExceptT.bind, ExceptT.bindCont,
      ExceptT.pure, ExceptT.mk, ExceptT.lift, ExceptT.map, EStateM.bind, EStateM.map, EStateM.pure,
      liftM, MonadLiftT.monadLift, MonadLift.monadLift, hl3, hb]
#print axioms total
end S1OuterPrefix
