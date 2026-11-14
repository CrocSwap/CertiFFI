import Pilot.S2Undef
import Pilot.S2DecodeAny
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
namespace S2NSAny
/- No VTCR field restriction, including reserved TG0 and arbitrary implementation fallback. -/
drive_spec native, complete :
  fun (hcr vtcr sctlr hcrx s2pir scr vttbrLow : BitVec 64) (vttbr : BitVec 128)
      (a64 : Bool) (s : SequentialState Regs oracleChoiceSource)
      (hHCR : s.regs.bank_BitVec_64 .HCR_EL2 = hcr)
      (hVTCR : s.regs.bank_BitVec_64 .VTCR_EL2 = vtcr)
      (hSCTLR : s.regs.bank_BitVec_64 .SCTLR_EL2 = sctlr)
      (hHCRX : s.regs.bank_BitVec_64 .HCRX_EL2 = hcrx)
      (hS2PIR : s.regs.bank_BitVec_64 .S2PIR_EL2 = s2pir)
      (hSCR : s.regs.bank_BitVec_64 .SCR_EL3 = scr)
      (hVTTBR : s.regs.bank_BitVec_128 ._VTTBR_EL2 = vttbr)
      (hVTTBRLow : s.regs.bank_BitVec_64 .VTTBR = vttbrLow) =>
    AArch64_NSS2TTWParams a64 s
attribute [step_summary] complete
#print axioms complete
end S2NSAny
