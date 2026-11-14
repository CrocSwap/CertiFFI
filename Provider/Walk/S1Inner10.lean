import Walk.S1TableUpdate10
import Walk.S1TableFault10
import Walk.S1LeafBothLoop
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1Inner10
abbrev State := S1WalkInvalid.State
abbrev Return := S1WalkInvalid.Return
abbrev Vars := S1WalkInvalid.Vars
abbrev Result := Except (Sail.Error exception ⊕ Return) Vars

def Progress (current : TTWState) (fault : FaultRecord) : Result → Prop
  | .error (.inl _) => False
  | .error (.inr (f, _, _, _)) => f.level = fault.level ∧
      (f.statuscode = .Fault_Translation ∨ f.statuscode = .Fault_AddressSize)
  | .ok (_, _, _, typ, f, _, _, _, _, next) => f = fault ∧
      ((typ = .DescriptorType_Leaf ∧ next.level = current.level ∧
        next.baseaddress.paspace = .PAS_NonSecure) ∨
       (typ = .DescriptorType_Table ∧ next.level = current.level + 1 ∧
        next.baseaddress.paspace = .PAS_NonSecure))

def Detailed (wp : S1TTWParams) (va d : BitVec 64) (current : TTWState) : Result → Prop
  | .error _ => True
  | .ok (_, addr, _, typ, _, _, _, _, _, next) =>
      (typ = .DescriptorType_Leaf ∧ S1DecodeFacts.classify d current.level = .DescriptorType_Leaf ∧ S1LeafShape.Shape wp current d next) ∨
      (typ = .DescriptorType_Table ∧ S1DecodeFacts.classify d current.level = .DescriptorType_Table ∧ addr = S1TablePrefix10.address next va ∧ S1TablePrefix10.outOfRange wp addr = false ∧
        S1NextTable10Facts.Shape current d next)

theorem total (wp : S1TTWParams) (va : BitVec 64) (acc : AccessDescriptor)
    (walkaddr : AddressDescriptor) (ti : TranslationInfo) (s2fs1mro aligned : Bool)
    (descaddr : FullAddress) (d : BitVec 64) (oldType : DescriptorType)
    (fault : FaultRecord) (oldNew : BitVec 64) (a64 : Bool) (s2fault : FaultRecord)
    (skl : BitVec 2) (current : TTWState) (s : State) (cfg : S2Interface.Config)
    (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1) (hTG : wp.tgx = .TGx_4KB)
    (hAIE : wp.aie = 0#1) (hMAIR : wp.mair = 0x000000040044ffff#64)
    (hLevel : 0 ≤ current.level ∧ current.level ≤ 3)
    (hPAS : current.baseaddress.paspace = .PAS_NonSecure)
    (hPA : s.regs.bank_Int .__supported_pa_size = 48)
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
    (hOld : S1ByteMemory.DescAt s.mem walkaddr.paddress.address.toNat (S2Endian.encode wp.ee d)) :
    ∃ (result : Result) (t : State),
      S1WalkSource.named.loop1 wp va .Regime_EL10 acc 64 descaddr oldType skl current
        walkaddr ti aligned d fault a64 s2fault s2fs1mro oldNew s = .ok result t ∧
      Progress current fault result ∧ Detailed wp va d current result ∧ t.regs = s.regs ∧
      S1MemoryObservation.Equivalent (S1TableUpdate10.observe wp) s.mem t.mem := by
  cases hc : S1DecodeFacts.classify d current.level with
  | DescriptorType_Invalid =>
    rcases S1WalkInvalid.source_loop_total wp va .Regime_EL10 acc walkaddr ti s2fs1mro
      aligned descaddr d oldType fault oldNew a64 s2fault skl current s
      hD128 hDS hTG hc with ⟨a, w, out, t, hr, hregs, hmem, _⟩
    refine ⟨_, t, hr, ?_, by trivial, hregs, ?_⟩
    · simp [Progress, S1WalkInvalid.faultResult]
    · rw [hmem]
      intro a ha v
      rfl
  | DescriptorType_Leaf =>
    rcases S1LeafBothLoop.source_loop_total .Regime_EL10 (Or.inl rfl) wp va acc walkaddr ti
      s2fs1mro aligned descaddr d oldType fault oldNew a64 s2fault skl current s
      hD128 hDS hTG hAIE hMAIR hSS hPAS hc with ⟨next, t, hr, hregs, hmem, _, hs⟩
    refine ⟨_, t, hr, ?_, Or.inl ⟨rfl, hc, hs⟩, hregs, ?_⟩
    · exact ⟨rfl, Or.inl ⟨rfl, hs.2.1, hs.2.2.2.1⟩⟩
    · rw [hmem]
      intro a ha v
      rfl
  | DescriptorType_Table =>
    have hl : 0 ≤ current.level ∧ current.level ≤ 2 := by
      have := S1DecodeFacts.table_before_final d current.level hLevel.2 hc
      omega
    rcases S1TablePrefix10.total wp current d va s2fs1mro s
      hD128 hDS hTG hl hPAS hPA with ⟨c⟩
    cases hRange : S1TablePrefix10.outOfRange wp (S1TablePrefix10.address c.next va) with
    | true =>
      rcases S1TableFault10.source_loop_total wp va acc walkaddr ti s2fs1mro aligned
        descaddr d oldType fault oldNew a64 s2fault skl current s hD128 hDS hTG hc c hRange with
        ⟨a, w, out, t, hr, hregs, hmem, _⟩
      refine ⟨_, t, hr, ?_, by trivial, hregs, ?_⟩
      · simp [Progress, S1TableFault10.result]
      · rw [hmem]
        intro a ha v
        rfl
    | false =>
      rcases S1TableUpdate10.source_loop_total wp va acc walkaddr ti s2fs1mro aligned
        descaddr d oldType fault oldNew a64 s2fault skl current s cfg hD128 hDS hTG hc c
        hRange hConfig hVM hDC hSS hFault hEL hNoRME hA64 hEL3A64 hNoEL3A32 hRAM hAlign hOld with
        ⟨ao, a64o, s2fo, t, hr, hregs, hobs⟩
      exact ⟨_, t, hr, ⟨rfl, Or.inr ⟨rfl, c.shape.2.1, c.shape.2.2.2.1⟩⟩, Or.inr ⟨rfl, hc, rfl, hRange, c.shape⟩, hregs, hobs⟩
#print axioms total
end S1Inner10
