import N1D226.CmpShiftZero64.Tail
import CompiledLean.CmpArithmeticV1
import ArmCertValueTail.Flags
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace N1D226.CmpShiftZero64.CmpShape
open ArmBridge.Draft
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false
set_option backward.dsimp.instances true
attribute [local implicit_reducible] Sail.Int.toNatChecked
theorem zero_shift_int (n : Nat) :
    @HShiftLeft.hShiftLeft (BitVec 64) Int (BitVec 64)
      Sail.instHShiftLeftBitVecInt_sail (0#64) (n : Int) = 0#64 := by
  change BitVec.shiftLeft (0#64) n = 0#64
  exact BitVec.zero_shiftLeft n

namespace Math
abbrev nzcv := CompiledLean.CmpArithmetic.V1.nzcv
abbrev result := CompiledLean.CmpArithmetic.V1.result
end Math

theorem extract64 (x : BitVec 64) : Sail.BitVec.extractLsb x 63 0 = x :=
  CompiledLean.CmpArithmetic.V1.full_extract x

def flags (s : NativeState) (Rn : BitVec 5) (imm6 : BitVec 6) : BitVec 4 :=
  Math.nzcv s.regs.gpr[(GPRSummary.key Rn.toNat).val] (~~~(0#64)) 1#1

theorem shape (s : NativeState) (Rn : BitVec 5) (imm6 : BitVec 6) (rn : Rn.toNat < 31)
    (spe : s.regs.bank_Bool .SPESampleInFlight = false) :
    (N1D226.CmpShiftZero64.expected s Rn imm6).1.gpr = s.regs.gpr ∧
    (N1D226.CmpShiftZero64.expected s Rn imm6).1.SP_EL0 = s.regs.SP_EL0 ∧
    (N1D226.CmpShiftZero64.expected s Rn imm6).1.PSTATE.N = Sail.BitVec.extractLsb (flags s Rn imm6) 3 3 ∧
    (N1D226.CmpShiftZero64.expected s Rn imm6).1.PSTATE.Z = Sail.BitVec.extractLsb (flags s Rn imm6) 2 2 ∧
    (N1D226.CmpShiftZero64.expected s Rn imm6).1.PSTATE.C = Sail.BitVec.extractLsb (flags s Rn imm6) 1 1 ∧
    (N1D226.CmpShiftZero64.expected s Rn imm6).1.PSTATE.V = Sail.BitVec.extractLsb (flags s Rn imm6) 0 0 := by
  have hn : ¬ (Rn.toNat : Int) = 31 := by omega
  unfold N1D226.CmpShiftZero64.expected N1D226.CmpShiftZero64.effect_native
  simp only [ArmFull.Register.PSTATE_set,zero_shift_int,hn,spe,ite_true,ite_false,dite_eq_ite,ite_self]
  and_intros
  all_goals simp [Sail.BitVec.castWidth,zero_shift_int,extract64,flags,Math.nzcv,Math.result,
    CompiledLean.CmpArithmetic.V1.nzcv,CompiledLean.CmpArithmetic.V1.result,
    CompiledLean.CmpArithmetic.V1.full_extract,Sail.BitVec.zeroExtend,BitVec.zeroExtend,BitVec.length,
    Sail.BitVec.length,Int.toNatChecked,Sail.Int.toNatChecked,
    CompiledLean.CmpArithmetic.V1.ex4n,CompiledLean.CmpArithmetic.V1.ex4z,
    CompiledLean.CmpArithmetic.V1.ex4c,CompiledLean.CmpArithmetic.V1.ex4v]
  all_goals try simp [extract64,BitVec.toNat_not,BitVec.toNat_setWidth]
  all_goals try rw [extract64]
  all_goals rw [zero_shift_int imm6.toNat]
  all_goals rfl

#print axioms shape
end N1D226.CmpShiftZero64.CmpShape
