import Walk.S2PhysicalSize
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace S2OAOutOfRange
drive_spec native, complete :
  fun (paSize : Int) (address : BitVec 56) (ps : BitVec 3)
      (s : SequentialState Regs oracleChoiceSource)
      (hPA : s.regs.bank_Int .__supported_pa_size = paSize) =>
    AArch64_OAOutOfRange address 0#1 ps .TGx_4KB s
attribute [step_summary] complete
#print axioms complete
end S2OAOutOfRange
