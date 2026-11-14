import Walk.S1OuterSplit
import Walk.S1InnerBoth
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 300000
set_option maxRecDepth 1000000
namespace S1OuterStep
abbrev State := S1OuterBody.State
abbrev Vars := S1OuterBody.Vars
abbrev Return := S1OuterBody.Return
abbrev Result := Except (Sail.Error exception ⊕ Return) Vars

def finish (r : S1OuterPrefix.Input) : S1Inner10.Vars → Vars
  | (aligned, addr, d, typ, fault, _, a64, _, skl, current) =>
    (aligned, addr, d, typ, fault, a64, r.s2fs1mro, skl, r.walkaddr, current)

def Progress (current : TTWState) (fault : FaultRecord) : Result → Prop
  | .error (.inl _) => False
  | .error (.inr (f, _, _, _)) => f.level = current.level ∧
      (f.statuscode = .Fault_Translation ∨ f.statuscode = .Fault_AddressSize)
  | .ok (_, _, _, typ, f, _, _, _, _, next) =>
      f = {fault with level := current.level} ∧
      ((typ = .DescriptorType_Leaf ∧ next.level = current.level ∧
        next.baseaddress.paspace = .PAS_NonSecure) ∨
       (typ = .DescriptorType_Table ∧ next.level = current.level + 1 ∧
        next.baseaddress.paspace = .PAS_NonSecure))

def Detailed (wp : S1TTWParams) (va d : BitVec 64) (current : TTWState) : Result → Prop
  | .error _ => True
  | .ok (_, addr, _, typ, _, _, _, _, _, next) =>
      (typ = .DescriptorType_Leaf ∧ S1DecodeFacts.classify d current.level = .DescriptorType_Leaf ∧
        S1LeafShape.Shape wp current d next) ∨
      (typ = .DescriptorType_Table ∧ S1DecodeFacts.classify d current.level = .DescriptorType_Table ∧
        addr = S1TablePrefix10.address next va ∧ S1TablePrefix10.outOfRange wp addr = false ∧ S1NextTable10Facts.Shape current d next)

theorem detailed_finish (wp : S1TTWParams) (va d : BitVec 64) (current : TTWState)
    (r : S1OuterPrefix.Input) (result : S1Inner10.Result)
    (h : S1Inner10.Detailed wp va d current result) :
    Detailed wp va d current (result.map (finish r)) := by
  cases result with
  | error e => trivial
  | ok v =>
    rcases v with ⟨a, addr, d, typ, f, newd, a64, s2f, skl, next⟩
    exact h

theorem progress_finish (current : TTWState) (fault : FaultRecord)
    (r : S1OuterPrefix.Input) (result : S1Inner10.Result)
    (h : S1Inner10.Progress current {fault with level := current.level} result) :
    Progress current fault (result.map (finish r)) := by
  cases result with
  | error e => cases e <;> simpa [S1Inner10.Progress, Progress, Except.map] using h
  | ok v =>
    rcases v with ⟨a, addr, d, typ, f, newd, a64, s2f, skl, next⟩
    exact h

theorem encode_decoded (ee : BitVec 1) (data : BitVec 64) :
    S2Endian.encode ee (S2FetchFrame.decoded ee data) = data := by
  by_cases h : ee = 1#1 <;>
    simp [S2Endian.encode, S2FetchFrame.decoded, h, S2Endian.reverse_involutive]

theorem total (regime : Regime) (hRegime : S1LeafBoth.Regimes regime)
    (wp : S1TTWParams) (va : BitVec 64) (acc : AccessDescriptor) (startlevel : Int)
    (aligned : Bool) (descaddr : FullAddress) (d : BitVec 64) (typ : DescriptorType)
    (fault : FaultRecord) (a64 s2fs1mro : Bool) (skl : BitVec 2)
    (walkaddr : AddressDescriptor) (current : TTWState) (cfg : S2Interface.Config)
    (data : BitVec 64) (s : State)
    (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1) (hTG : wp.tgx = .TGx_4KB)
    (hAIE : wp.aie = 0#1) (hMAIR : wp.mair = 0x000000040044ffff#64)
    (hLevel : 0 ≤ current.level ∧ current.level ≤ 3)
    (hPAS : current.baseaddress.paspace = .PAS_NonSecure)
    (hPA : s.regs.bank_Int .__supported_pa_size = 48)
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
    (hAlign : descaddr.address.toNat % 8 = 0)
    (hOld : S2ByteMemory.DescAt s.mem descaddr.address.toNat data) :
    ∃ (result : Result) (t : State),
      S1WalkSource.named.body0 wp va regime acc 64 startlevel
        (aligned, descaddr, d, typ, fault, a64, s2fs1mro, skl, walkaddr, current) s =
        .ok result t ∧ Progress current fault result ∧
      Detailed wp va (S2FetchFrame.decoded wp.ee data) current result ∧ t.regs = s.regs ∧
      S1MemoryObservation.Equivalent (S1TableUpdate10.observe wp) s.mem t.mem := by
  rcases S1OuterPrefix.total wp va regime acc startlevel aligned descaddr d typ fault a64
    s2fs1mro skl walkaddr current cfg data s hFault hConfig hVM hDC hSS hEL hNoRME hA64
    hEL3A64 hNoEL3A32 hRAM hOld with ⟨r, t1, hp, hr1, hm1, hd, hf, ha⟩
  have hc1 : S2Interface.ConfigAt cfg t1 := by
    rcases hConfig with ⟨a, b, c, d, e, f, g, h⟩
    exact ⟨by simpa only [hr1] using a, by simpa only [hr1] using b,
      by simpa only [hr1] using c, by simpa only [hr1] using d,
      by simpa only [hr1] using e, by simpa only [hr1] using f,
      by simpa only [hr1] using g, by simpa only [hr1] using h⟩
  have hold1 : S1ByteMemory.DescAt t1.mem r.walkaddr.paddress.address.toNat
      (S2Endian.encode wp.ee r.descriptor) := by
    rw [hm1, ha, hd, encode_decoded]
    exact hOld
  rcases S1InnerBoth.total regime hRegime wp va acc r.walkaddr
    (S1OuterSplit.info wp regime current r.walkaddr) r.s2fs1mro r.aligned descaddr
    r.descriptor typ r.fault r.newd r.a64 r.s2fault skl current t1 cfg
    hD128 hDS hTG hAIE hMAIR hLevel hPAS (by simpa only [hr1] using hPA)
    hc1 hVM hDC hSS (by simpa only [hf] using hFault)
    (by simpa only [hr1] using hEL) (by simpa only [hr1] using hNoRME)
    (by simpa only [hr1] using hA64) (by simpa only [hr1] using hEL3A64)
    (by simpa only [hr1] using hNoEL3A32) (by simpa only [ha] using hRAM)
    (by simpa only [ha] using hAlign) hold1 with ⟨result, t, hi, hprogress, hdetail, hr2, hobs⟩
  rw [hf] at hprogress
  rw [hd] at hdetail
  refine ⟨result.map (finish r), t, ?_, progress_finish current fault r result hprogress,
    detailed_finish wp va (S2FetchFrame.decoded wp.ee data) current r result hdetail,
    hr2.trans hr1, ?_⟩
  · rw [S1OuterSplit.equation]
    cases result with
    | error e =>
      simp [Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure, Pure.pure,
        EStateM.bind, EStateM.pure, hp, S1OuterSplit.resume, hi, Except.map]
    | ok v =>
      rcases v with ⟨a, addr, d, typ, f, newd, a64, s2f, skl, next⟩
      simp [Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure, Pure.pure,
        EStateM.bind, EStateM.pure, hp, S1OuterSplit.resume, hi, Except.map, finish]
  · simpa only [hm1] using hobs
#print axioms total
end S1OuterStep
