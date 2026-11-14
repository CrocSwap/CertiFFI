import Walk.S1TTBRRead
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1InitialBase
abbrev State := S1Normality.State

drive_spec native, complete : fun (wp : S1TTWParams) (regime : Regime)
    (ttbr : BitVec 128) (s : State)
    (hd : wp.d128 = 0#1) (hds : wp.ds = 0#1)
    (htg : wp.tgx = .TGx_4KB) (htx : wp.txsz = 16#6) =>
  AArch64_S1TTBaseAddress wp regime ttbr s
attribute [step_summary] complete
#print axioms complete
end S1InitialBase
