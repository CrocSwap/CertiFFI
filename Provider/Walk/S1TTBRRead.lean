import Pilot.Driver
import Walk.S2SecurityEL
import Walk.S1EntryCallees
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1TTBRRead
abbrev State := S1Normality.State

drive_spec host_native, host_eq : fun (va : BitVec 64) (s : State) =>
  AArch64_S1TTBR .Regime_EL20 va s
attribute [step_summary] host_eq

drive_spec guest_native, guest_eq : fun (va : BitVec 64) (s : State)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false) =>
  AArch64_S1TTBR .Regime_EL10 va s
attribute [step_summary] guest_eq

#print axioms host_eq
#print axioms guest_eq
end S1TTBRRead
