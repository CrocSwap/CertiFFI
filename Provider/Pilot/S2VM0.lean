import Pilot.S2GetAny
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
namespace S2VM0
theorem vm_field (hcr : BitVec 64) (hVM : _get_HCR_EL2_Type_VM hcr = 0#1) :
    Sail.BitVec.extractLsb hcr 0 0 = 0#1 := hVM
theorem dc_field (hcr : BitVec 64) (hDC : _get_HCR_EL2_Type_DC hcr = 0#1) :
    Sail.BitVec.extractLsb hcr 12 12 = 0#1 := hDC
drive_spec native, complete :
  fun (hcr vtcr sctlr hcrx s2pir scr vttbrLow : BitVec 64) (vttbr : BitVec 128)
      (fault : FaultRecord) (ipa : AddressDescriptor) (a64 : Bool)
      (level : Option Int) (aligned : Bool) (acc : AccessDescriptor)
      (s : SequentialState Regs oracleChoiceSource)
      (hHCR : s.regs.bank_BitVec_64 .HCR_EL2 = hcr)
      (hVTCR : s.regs.bank_BitVec_64 .VTCR_EL2 = vtcr)
      (hSCTLR : s.regs.bank_BitVec_64 .SCTLR_EL2 = sctlr)
      (hHCRX : s.regs.bank_BitVec_64 .HCRX_EL2 = hcrx)
      (hS2PIR : s.regs.bank_BitVec_64 .S2PIR_EL2 = s2pir)
      (hSCR : s.regs.bank_BitVec_64 .SCR_EL3 = scr)
      (hVTTBR : s.regs.bank_BitVec_128 ._VTTBR_EL2 = vttbr)
      (hVTTBRLow : s.regs.bank_BitVec_64 .VTTBR = vttbrLow)
      (hVM : Sail.BitVec.extractLsb hcr 0 0 = 0#1)
      (hDC : Sail.BitVec.extractLsb hcr 12 12 = 0#1)
      (hSS : acc.ss = .SS_NonSecure) =>
    AArch64_S2Translate fault ipa a64 level aligned acc s
attribute [step_summary] complete
#print axioms complete
end S2VM0
