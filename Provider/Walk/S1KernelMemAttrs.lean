import Pilot.UndefSummaries
import Walk.S1RESMAIR
import Walk.S2Shareability
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1KernelMemAttrs
drive_spec zero_native, zero_eq :
  fun (sh : BitVec 2) (wp : S1TTWParams) (s : SequentialState Regs oracleChoiceSource) =>
    S1DecodeMemAttrs 0#8 sh true wp s
attribute [step_summary] zero_eq
#print axioms zero_eq
drive_spec device_native, device_eq :
  fun (sh : BitVec 2) (wp : S1TTWParams) (s : SequentialState Regs oracleChoiceSource) =>
    S1DecodeMemAttrs 4#8 sh true wp s
attribute [step_summary] device_eq
#print axioms device_eq
drive_spec uncached_native, uncached_eq :
  fun (sh : BitVec 2) (wp : S1TTWParams) (s : SequentialState Regs oracleChoiceSource) =>
    S1DecodeMemAttrs 68#8 sh true wp s
attribute [step_summary] uncached_eq
#print axioms uncached_eq
drive_spec normal_native, normal_eq :
  fun (sh : BitVec 2) (wp : S1TTWParams) (s : SequentialState Regs oracleChoiceSource) =>
    S1DecodeMemAttrs 255#8 sh true wp s
attribute [step_summary] normal_eq
#print axioms normal_eq
end S1KernelMemAttrs

