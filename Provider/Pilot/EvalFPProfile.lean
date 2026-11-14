import Pilot.EvalProfile
namespace EvalProfile
/- Pilot-dev only: C32 G3 word; C30 CPTR effective FP permission fields. -/
def cpacrG3 : BitVec 64 := 0x330000#64
def cptr2FpNoTrap : BitVec 1 := 0#1
def cptr3FpNoTrap : BitVec 1 := 0#1
def fpcrLinux : BitVec 64 := 0#64
/-- Field-level GB10 C34 host controls; ZEN remains context-dependent. -/
def gb10HostFPEN : BitVec 2 := 3#2
def gb10HostZENFpsimd : BitVec 2 := 1#2
def gb10HostZENSve : BitVec 2 := 3#2
def hcrGB10Host : BitVec 64 := 0x0000000488000038#64
structure FPProfile where
  base : Profile
  fpcr : BitVec 64
def profOffFPG3 : FPProfile where
  base := {profOff with r64 := profOff.r64 ++
    [(.CPACR_EL1, cpacrG3)]}
  fpcr := fpcrLinux
def FPHolds (p : FPProfile) (r : ArmFull.Regs) : Prop :=
  Holds p.base r ∧ r.FPCR = p.fpcr ∧
  ArmFull.Functions._get_CPTR_EL2_Type_TFP (r.bank_BitVec_64 .CPTR_EL2) = cptr2FpNoTrap ∧
  ArmFull.Functions._get_CPTR_EL3_Type_TFP (r.bank_BitVec_64 .CPTR_EL3) = cptr3FpNoTrap
end EvalProfile
