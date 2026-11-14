import Pilot.S1NextTableBase
import Pilot.UndefSummaries
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
set_option linter.unusedVariables false
namespace S1NextTable
/- This is a helper for the EL2&0 case. Parameter premises are obligations of
   the profile/walk-parameter derivation, not added full-theorem assumptions. -/
drive_spec native, complete :
  fun (current : TTWState) (s2fs1mro : Bool) (wp : S1TTWParams)
      (descriptor : BitVec 64) (s : SequentialState Regs oracleChoiceSource)
      (hd128 : wp.d128 = 0#1) (hds : wp.ds = 0#1) (htg : wp.tgx = .TGx_4KB) =>
    AArch64_S1NextWalkStateTable current s2fs1mro .Regime_EL20 wp descriptor s
#print axioms complete
end S1NextTable
