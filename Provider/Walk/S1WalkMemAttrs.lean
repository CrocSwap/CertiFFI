import Walk.S1WalkDecode
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1WalkMemAttrs

drive_spec native, complete : fun (sh irgn orgn : BitVec 2)
    (s : SequentialState Regs oracleChoiceSource) => WalkMemAttrs sh irgn orgn s
attribute [step_summary] complete
#print axioms complete
end S1WalkMemAttrs
