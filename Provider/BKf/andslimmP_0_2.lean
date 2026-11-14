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
drive_spec andslimmP_0_2_native, andslimmP_0_2_complete :
  fun (real : Type) [Sail.SailReal real] (Rd Rn : BitVec 5) (s : SequentialState Regs oracleChoiceSource) =>
    ((do let _ ← (decode_ands_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn 2#6 0#6 1#1 3#2 1#1 : SailM Unit);
         let u ← get
         pure (u.regs.bank_Bool, u.regs.FeatureImpl, (u.regs.PSTATE.D, u.regs.PSTATE.A, u.regs.PSTATE.I, u.regs.PSTATE.F, u.regs.PSTATE.EXLOCK, u.regs.PSTATE.PAN, u.regs.PSTATE.UAO, u.regs.PSTATE.DIT, u.regs.PSTATE.TCO, u.regs.PSTATE.PM, u.regs.PSTATE.PPEND, u.regs.PSTATE.BTYPE, u.regs.PSTATE.ZA, u.regs.PSTATE.SM, u.regs.PSTATE.ALLINT, u.regs.PSTATE.SS, u.regs.PSTATE.IL, u.regs.PSTATE.EL, u.regs.PSTATE.nRW, u.regs.PSTATE.SP, u.regs.PSTATE.Q, u.regs.PSTATE.GE, u.regs.PSTATE.SSBS, u.regs.PSTATE.IT, u.regs.PSTATE.J, u.regs.PSTATE.T, u.regs.PSTATE.E, u.regs.PSTATE.M), u.regs.BTypeNext,
           u.regs.__BranchTaken, u.regs._PC, u.regs.bank_BitVec_64, u.regs.bank_BitVec_32, u.regs.bank_Int,
           u.regs.ShouldAdvanceSS, u.regs.ShouldAdvanceIT, u.regs.__ThisInstrEnc, u.mem, u.events, u.regs.Branchtypetaken, u.regs.__emulator_termination_opcode, u.regs.bank_BitVec_128, ArmCertCT.CT2.mask ArmBridge.CruxNonProj.bkHeap u.regs, u.regs.bank_Option_InterruptID .__GIC_Pending)) : SailM _) s
#print axioms andslimmP_0_2_complete
end ArmBridge.BKf
