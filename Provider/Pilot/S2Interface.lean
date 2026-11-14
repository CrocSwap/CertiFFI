import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace S2Interface
abbrev State := SequentialState Regs oracleChoiceSource

/-- Unobserved hypervisor words are parameters, without numerical defaults (C32).
    SCR is likewise unobserved EL3 state. FeatureImpl remains arbitrary. -/
structure Config where
  hcr : BitVec 64
  vtcr : BitVec 64
  sctlr : BitVec 64
  hcrx : BitVec 64
  s2pir : BitVec 64
  scr : BitVec 64
  vttbr : BitVec 128
  vttbrLow : BitVec 64

structure ConfigAt (c : Config) (s : State) : Prop where
  hHCR : s.regs.bank_BitVec_64 .HCR_EL2 = c.hcr
  hVTCR : s.regs.bank_BitVec_64 .VTCR_EL2 = c.vtcr
  hSCTLR : s.regs.bank_BitVec_64 .SCTLR_EL2 = c.sctlr
  hHCRX : s.regs.bank_BitVec_64 .HCRX_EL2 = c.hcrx
  hS2PIR : s.regs.bank_BitVec_64 .S2PIR_EL2 = c.s2pir
  hSCR : s.regs.bank_BitVec_64 .SCR_EL3 = c.scr
  hVTTBR : s.regs.bank_BitVec_128 ._VTTBR_EL2 = c.vttbr
  hVTTBRLow : s.regs.bank_BitVec_64 .VTTBR = c.vttbrLow

abbrev Native := Config → FaultRecord → AddressDescriptor → Option Int → Bool →
  AccessDescriptor → SailM (FaultRecord × AddressDescriptor)

/-- Step-9 exact equation. It covers both GPR and TTW access descriptors.
    Equality includes the complete result, fault, memory, events and oracle state.
    This is a target statement, not a proved translation summary. -/
def Exact (native : Native) : Prop :=
  ∀ (c : Config) (fault : FaultRecord) (ipa : AddressDescriptor)
    (s1level : Option Int) (aligned : Bool) (acc : AccessDescriptor) (s : State),
    ConfigAt c s → _get_VTCR_EL2_Type_TG0 c.vtcr = 0#2 →
    acc.ss = .SS_NonSecure →
    AArch64_S2Translate fault ipa true s1level aligned acc s =
      native c fault ipa s1level aligned acc s

/- The independent C14 projection will constrain the resulting PA/PAS/attributes
   only when the returned fault is Fault_None. C36 must be proved over the actual
   descriptor-memory writes; Exact alone makes no page-map invariance claim. -/
end S2Interface
