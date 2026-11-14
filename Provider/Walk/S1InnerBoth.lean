import Walk.S1Inner20
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 300000
namespace S1InnerBoth
abbrev State := S1Inner10.State
abbrev Result := S1Inner10.Result
abbrev Progress := S1Inner10.Progress
abbrev Detailed := S1Inner10.Detailed

theorem total (regime : Regime) (hRegime : S1LeafBoth.Regimes regime) (wp : S1TTWParams) (va : BitVec 64) (acc : AccessDescriptor)
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
      S1WalkSource.named.loop1 wp va regime acc 64 descaddr oldType skl current
        walkaddr ti aligned d fault a64 s2fault s2fs1mro oldNew s = .ok result t ∧
      Progress current fault result ∧ Detailed wp va d current result ∧ t.regs = s.regs ∧
      S1MemoryObservation.Equivalent (S1TableUpdate10.observe wp) s.mem t.mem := by
  rcases hRegime with rfl | rfl
  · exact S1Inner10.total wp va acc walkaddr ti s2fs1mro aligned descaddr d oldType
      fault oldNew a64 s2fault skl current s cfg hD128 hDS hTG hAIE hMAIR hLevel hPAS hPA
      hConfig hVM hDC hSS hFault hEL hNoRME hA64 hEL3A64 hNoEL3A32 hRAM hAlign hOld
  · simpa only [S1TableUpdate.observe, S1TableUpdate10.observe] using
      S1Inner20.total wp va acc walkaddr ti s2fs1mro aligned descaddr d oldType
        fault oldNew a64 s2fault skl current s hD128 hDS hTG hAIE hMAIR hLevel hPAS hPA
        hSS hFault hEL hNoRME hA64 hEL3A64 hNoEL3A32 hRAM hAlign hOld
#print axioms total
end S1InnerBoth
