import Walk.S2UndefAddress
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace S2NextEntryAddress
/- Exact 64-bit 4KiB subsequent-level entry calculation, with all invalid
   level errors retained in the summary. -/
drive_spec native, complete :
  fun (level : Int) (skl : BitVec 2) (txsz : BitVec 6) (ia : BitVec 64)
      (table : FullAddress) (s : SequentialState Regs oracleChoiceSource) =>
    AArch64_TTEntryAddress level 0#1 skl .TGx_4KB txsz ia table s
attribute [step_summary] complete
#print axioms complete
end S2NextEntryAddress
