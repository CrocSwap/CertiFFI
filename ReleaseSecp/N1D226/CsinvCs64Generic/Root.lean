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
namespace N1D226.CsinvCs64Generic
-- Actual selected decoder with explicit current-state guards. Not an evaluator.
drive_spec effect_native, effect_complete :
  fun (s : SequentialState Regs oracleChoiceSource) (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5)
      (rd : Rd.toNat < 31)
      (rn : Rn.toNat < 31)
      (rm : Rm.toNat < 31)
      (el : s.regs.PSTATE.EL = 0#2)
      (a64 : s.regs.PSTATE.nRW = 0#1)
      (aa64 : s.regs.FeatureImpl[4]! = true)
      (btype : s.regs.PSTATE.BTYPE = 0#2)
      (btn : s.regs.BTypeNext = 0#2) =>
    ((do let _ ← (decode_csinv_aarch64_instrs_integer_conditional_select Rd Rn 0#1 2#4 Rm 1#1 1#1 : SailM Unit)
         let u ← get
         pure (u.regs,u.mem,u.events)) : SailM _) s
#print axioms effect_complete
end N1D226.CsinvCs64Generic
