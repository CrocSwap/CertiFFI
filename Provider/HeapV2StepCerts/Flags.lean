-- Memory (B1 (c)): the NZCV flags of a register file, as one value.
import ArmFull
set_option autoImplicit false
namespace HeapV2StepCerts.Flags

def nzcv (r : ArmFull.Regs) : BitVec 1 × BitVec 1 × BitVec 1 × BitVec 1 :=
  (r.PSTATE.N, r.PSTATE.Z, r.PSTATE.C, r.PSTATE.V)

end HeapV2StepCerts.Flags
