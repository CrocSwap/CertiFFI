import Walk.S1InitialBase
import Walk.S1WalkMemAttrs
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1InitialWalkState
abbrev State := S1Normality.State

drive_spec host_native, host_eq : fun (wp : S1TTWParams) (va : BitVec 64) (s : State)
    (hd : wp.d128 = 0#1) (hds : wp.ds = 0#1)
    (htg : wp.tgx = .TGx_4KB) (htx : wp.txsz = 16#6) =>
  AArch64_S1InitialTTWState wp va .Regime_EL20 .SS_NonSecure s
attribute [step_summary] host_eq

drive_spec guest_native, guest_eq : fun (wp : S1TTWParams) (va : BitVec 64) (s : State)
    (hd : wp.d128 = 0#1) (hds : wp.ds = 0#1)
    (htg : wp.tgx = .TGx_4KB) (htx : wp.txsz = 16#6)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false) =>
  AArch64_S1InitialTTWState wp va .Regime_EL10 .SS_NonSecure s
attribute [step_summary] guest_eq
#print axioms host_eq
#print axioms guest_eq
end S1InitialWalkState
