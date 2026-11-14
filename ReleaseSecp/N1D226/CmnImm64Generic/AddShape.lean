import N1D226.CmnImm64Generic.Tail
import CompiledLean.CmpArithmeticV1
import ArmCertValueTail.Flags
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace N1D226.CmnImm64Generic.AddShape
open ArmBridge.Draft
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false
set_option backward.dsimp.instances true
attribute [local implicit_reducible] Sail.Int.toNatChecked
namespace Math
abbrev nzcv := CompiledLean.CmpArithmetic.V1.nzcv
abbrev result := CompiledLean.CmpArithmetic.V1.result
end Math

theorem extract64 (x : BitVec 64) : Sail.BitVec.extractLsb x 63 0 = x :=
  CompiledLean.CmpArithmetic.V1.full_extract x

def flags (s : NativeState) (Rn : BitVec 5) (imm12 : BitVec 12) : BitVec 4 :=
  Math.nzcv s.regs.gpr[(GPRSummary.key Rn.toNat).val] (imm12.setWidth 64) 0#1

theorem shape (s : NativeState) (Rn : BitVec 5) (imm12 : BitVec 12) (rn : Rn.toNat < 31)
    (spe : s.regs.bank_Bool .SPESampleInFlight = false) :
    (N1D226.CmnImm64Generic.expected s Rn imm12).1.gpr = s.regs.gpr ∧
    (N1D226.CmnImm64Generic.expected s Rn imm12).1.SP_EL0 = s.regs.SP_EL0 ∧
    (N1D226.CmnImm64Generic.expected s Rn imm12).1.PSTATE.N = Sail.BitVec.extractLsb (flags s Rn imm12) 3 3 ∧
    (N1D226.CmnImm64Generic.expected s Rn imm12).1.PSTATE.Z = Sail.BitVec.extractLsb (flags s Rn imm12) 2 2 ∧
    (N1D226.CmnImm64Generic.expected s Rn imm12).1.PSTATE.C = Sail.BitVec.extractLsb (flags s Rn imm12) 1 1 ∧
    (N1D226.CmnImm64Generic.expected s Rn imm12).1.PSTATE.V = Sail.BitVec.extractLsb (flags s Rn imm12) 0 0 := by
  have hn : ¬ (Rn.toNat : Int) = 31 := by omega
  unfold N1D226.CmnImm64Generic.expected N1D226.CmnImm64Generic.effect_native
  simp only [ArmFull.Register.PSTATE_set,hn,spe,ite_true,ite_false,dite_eq_ite,ite_self]
  and_intros
  all_goals simp [Sail.BitVec.castWidth,extract64,flags,Math.nzcv,Math.result,
    CompiledLean.CmpArithmetic.V1.nzcv,CompiledLean.CmpArithmetic.V1.result,
    CompiledLean.CmpArithmetic.V1.full_extract,Sail.BitVec.zeroExtend,BitVec.zeroExtend,BitVec.length,
    Sail.BitVec.length,Int.toNatChecked,Sail.Int.toNatChecked,
    CompiledLean.CmpArithmetic.V1.ex4n,CompiledLean.CmpArithmetic.V1.ex4z,
    CompiledLean.CmpArithmetic.V1.ex4c,CompiledLean.CmpArithmetic.V1.ex4v]
  all_goals try simp [extract64,BitVec.toNat_not,BitVec.toNat_setWidth]
  all_goals try rw [extract64]
  all_goals rfl

#print axioms shape
end N1D226.CmnImm64Generic.AddShape
