import Pilot.Driver
import Pilot.EvalProfile
import Pilot.UndefSummaries
import Pilot.NativeExport
import Pilot.GPRSummary
import Bridge.CruxNonProj
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions EvalProfile
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
namespace ArmBridge.BKf
drive_spec csincP3_native, csincP3_complete :
  fun (real : Type) [Sail.SailReal real] (Rd Rn Rm : BitVec 5) (s : SequentialState Regs oracleChoiceSource) =>
    ((do let _ ← (decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn 1#1 3#4 Rm 0#1 1#1 : SailM Unit);
         let u ← get
         pure (u.regs.bank_Bool, u.regs.FeatureImpl, u.regs.PSTATE, u.regs.BTypeNext,
           u.regs.__BranchTaken, u.regs._PC, u.regs.bank_BitVec_64, u.regs.bank_BitVec_32, u.regs.bank_Int,
           u.regs.ShouldAdvanceSS, u.regs.ShouldAdvanceIT, u.regs.__ThisInstrEnc, u.mem, u.events, u.regs.Branchtypetaken, u.regs.__emulator_termination_opcode, u.regs.bank_BitVec_128, ArmCertCT.CT2.mask ArmBridge.CruxNonProj.bkHeap u.regs, u.regs.bank_Option_InterruptID .__GIC_Pending)) : SailM _) s
#print axioms csincP3_complete
end ArmBridge.BKf
