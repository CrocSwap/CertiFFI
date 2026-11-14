import Walk.S2MPAMPartid
import Walk.S2MPAMPMG
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace S2MPAMCombine
attribute [-step_summary] S2MPAMMap.complete S2MPAMFields.partidComplete S2MPAMFields.pmgComplete
drive_spec native, complete :
  fun (el : BitVec 2) (pspace : PARTIDspaceType)
      (s : SequentialState Regs oracleChoiceSource)
      => genMPAM el false false pspace s
attribute [step_summary] complete
#print axioms complete
end S2MPAMCombine
