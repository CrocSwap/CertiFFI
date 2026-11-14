import Pilot.Driver
import Pilot.EvalProfile
import Pilot.UndefSummaries
import Pilot.NativeExport
import Pilot.GPRSummary
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false
namespace N1D226.CmpShiftZero64
-- Actual selected decoder with explicit current-state guards. Not an evaluator.
drive_spec effect_native, effect_complete :
  fun (s : SequentialState Regs oracleChoiceSource) (Rn : BitVec 5) (imm6 : BitVec 6)
      (rn : Rn.toNat < 31)
      (el : s.regs.PSTATE.EL = 0#2)
      (a64 : s.regs.PSTATE.nRW = 0#1)
      (aa64 : s.regs.FeatureImpl[4]! = true)
      (btype : s.regs.PSTATE.BTYPE = 0#2)
      (btn : s.regs.BTypeNext = 0#2) =>
    ((do let _ ← (decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg 31#5 Rn imm6 31#5 0#2 1#1 1#1 1#1 : SailM Unit)
         let u ← get
         pure (u.regs,u.mem,u.events)) : SailM _) s
#print axioms effect_complete
end N1D226.CmpShiftZero64
