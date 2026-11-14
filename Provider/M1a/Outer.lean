import M1a.Leaf
import Walk.S1OuterStep
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
set_option maxRecDepth 1000000
namespace ArmCert.Eval.M1a

/-- Outer walk step at a leaf slot: the exact loop variables it returns. -/
theorem outer_leaf (regime : Regime) (hRegime : S1LeafBoth.Regimes regime)
    (wp : S1TTWParams) (va : BitVec 64) (acc : AccessDescriptor) (startlevel : Int)
    (aligned : Bool) (descaddr : FullAddress) (d : BitVec 64) (typ : DescriptorType)
    (fault : FaultRecord) (a64 s2fs1mro : Bool) (skl : BitVec 2)
    (walkaddr : AddressDescriptor) (current : TTWState) (cfg : S2Interface.Config)
    (data : BitVec 64) (s : State)
    (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1) (hTG : wp.tgx = .TGx_4KB)
    (hAIE : wp.aie = 0#1) (hMAIR : wp.mair = 0x000000040044ffff#64)
    (hPAS : current.baseaddress.paspace = .PAS_NonSecure)
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
    (hOld : S2ByteMemory.DescAt s.mem descaddr.address.toNat data)
    (hLeaf : S1DecodeFacts.classify (S2FetchFrame.decoded wp.ee data) current.level =
      .DescriptorType_Leaf) :
    ∃ (r : S1OuterPrefix.Input) (next : TTWState) (t : State),
      S1WalkSource.named.body0 wp va regime acc 64 startlevel
        (aligned, descaddr, d, typ, fault, a64, s2fs1mro, skl, walkaddr, current) s =
        .ok (.ok (r.aligned, descaddr, S2FetchFrame.decoded wp.ee data, .DescriptorType_Leaf,
          {fault with level := current.level}, r.a64, r.s2fs1mro, skl,
          {walkaddr with paddress := descaddr}, next)) t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧
      S1LeafShape.Shape wp current (S2FetchFrame.decoded wp.ee data) next ∧
      LeafValue regime current r.s2fs1mro wp (S2FetchFrame.decoded wp.ee data) next s.regs := by
  rcases S1OuterPrefix.total wp va regime acc startlevel aligned descaddr d typ fault a64
    s2fs1mro skl walkaddr current cfg data s hFault hConfig hVM hDC hSS hEL hNoRME hA64
    hEL3A64 hNoEL3A32 hRAM hOld with ⟨r, t1, hp, hr1, hm1, hd, hf, ha⟩
  have hLeaf' : S1DecodeFacts.classify r.descriptor current.level = .DescriptorType_Leaf := by
    rw [hd]; exact hLeaf
  rcases leaf_loop regime hRegime wp va acc r.walkaddr
    (S1OuterSplit.info wp regime current r.walkaddr) r.s2fs1mro r.aligned descaddr
    r.descriptor typ r.fault r.newd r.a64 r.s2fault skl current t1
    hD128 hDS hTG hAIE hMAIR hSS hPAS hLeaf' with ⟨next, t, hl, hr2, hm2, _, hs, hv⟩
  refine ⟨r, next, t, ?_, hr2.trans hr1, hm2.trans hm1, by rw [← hd]; exact hs, ?_⟩
  · rw [S1OuterSplit.equation]
    have hres : S1OuterSplit.resume wp va regime acc descaddr typ skl current r t1 =
        .ok (.ok (r.aligned, descaddr, r.descriptor, .DescriptorType_Leaf, r.fault, r.a64,
          r.s2fs1mro, skl, r.walkaddr, next)) t := by
      simp [S1OuterSplit.resume, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
        ExceptT.pure, Pure.pure, EStateM.bind, EStateM.pure, hl]
    rw [← hd, ← hf, ← ha]
    simp [Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure, Pure.pure,
      EStateM.bind, EStateM.pure, hp, hres]
  · rw [← hd, ← hr1]; exact hv

#print axioms outer_leaf
end ArmCert.Eval.M1a
