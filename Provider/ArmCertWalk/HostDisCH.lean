import ArmCertWalk.HostLower
import ArmCertWalk.Profile

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

def HostDisCHEffect : EStateM.Result (Sail.Error exception) State S1TTWParams → Prop
  | .ok params _ => params.disch = 0#1
  | .error _ _ => False

theorem host_native_disch (tcr tcr2 hcr sctlr sctlr2 scr mair mair2 pir pire0 : BitVec 64)
    (ttbr0 ttbr1 : BitVec 128) (state : State)
    (d128 : state.regs.FeatureImpl[178] = true → _get_TCR2_EL2_Type_D128 tcr2 = 0#1) :
    HostDisCHEffect (HostLowerSource.native tcr tcr2 hcr sctlr sctlr2 scr mair mair2 pir pire0 ttbr0 ttbr1 state) := by
  observe_simp [HostDisCHEffect, HostLowerSource.native]
  intro active
  split at active
  · rename_i enabled
    have zero : Sail.BitVec.extractLsb tcr2 5 5 = 0#1 := d128 enabled.2.1
    simp [zero] at active
  · simp at active

#print axioms host_native_disch
end ArmCertWalk
