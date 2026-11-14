import N1D226.AddsShift64Generic.Tail
import CompiledLean.CmpArithmeticV1
import ArmCertValueTail.Flags
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace N1D226.AddsShift64Generic.AddShape
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

theorem shift_nat (x : BitVec 64) (n : Nat) :
    @HShiftLeft.hShiftLeft (BitVec 64) Int (BitVec 64)
      Sail.instHShiftLeftBitVecInt_sail x (n : Int) = x <<< n := by
  change BitVec.shiftLeft x n = BitVec.shiftLeft x n
  rfl

theorem extract64 (x : BitVec 64) : Sail.BitVec.extractLsb x 63 0 = x :=
  CompiledLean.CmpArithmetic.V1.full_extract x

def right (s : NativeState) (imm6 : BitVec 6) (Rm : BitVec 5) : BitVec 64 :=
  s.regs.gpr[(GPRSummary.key Rm.toNat).val] <<< imm6.toNat
def value (s : NativeState) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) : BitVec 64 :=
  Math.result s.regs.gpr[(GPRSummary.key Rn.toNat).val] (right s imm6 Rm) 0#1
def flags (s : NativeState) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) : BitVec 4 :=
  Math.nzcv s.regs.gpr[(GPRSummary.key Rn.toNat).val] (right s imm6 Rm) 0#1

theorem shape (s : NativeState) (Rd Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5)
    (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (spe : s.regs.bank_Bool .SPESampleInFlight = false) :
    (N1D226.AddsShift64Generic.expected s Rd Rn imm6 Rm).1.gpr =
      s.regs.gpr.set (GPRSummary.key Rd.toNat).val (value s Rn imm6 Rm) (GPRSummary.key Rd.toNat).isLt ∧
    (N1D226.AddsShift64Generic.expected s Rd Rn imm6 Rm).1.SP_EL0 = s.regs.SP_EL0 ∧
    (N1D226.AddsShift64Generic.expected s Rd Rn imm6 Rm).1.PSTATE.N = Sail.BitVec.extractLsb (flags s Rn imm6 Rm) 3 3 ∧
    (N1D226.AddsShift64Generic.expected s Rd Rn imm6 Rm).1.PSTATE.Z = Sail.BitVec.extractLsb (flags s Rn imm6 Rm) 2 2 ∧
    (N1D226.AddsShift64Generic.expected s Rd Rn imm6 Rm).1.PSTATE.C = Sail.BitVec.extractLsb (flags s Rn imm6 Rm) 1 1 ∧
    (N1D226.AddsShift64Generic.expected s Rd Rn imm6 Rm).1.PSTATE.V = Sail.BitVec.extractLsb (flags s Rn imm6 Rm) 0 0 := by
  have hd : ¬ (Rd.toNat : Int) = 31 := by omega
  have hn : ¬ (Rn.toNat : Int) = 31 := by omega
  have hm : ¬ (Rm.toNat : Int) = 31 := by omega
  unfold N1D226.AddsShift64Generic.expected N1D226.AddsShift64Generic.effect_native
  simp only [ArmFull.Register.PSTATE_set,hd,hn,hm,spe,ite_true,ite_false,dite_eq_ite,ite_self]
  and_intros
  all_goals simp [Sail.BitVec.castWidth,extract64,flags,value,right,Math.nzcv,Math.result,
    CompiledLean.CmpArithmetic.V1.nzcv,CompiledLean.CmpArithmetic.V1.result,
    CompiledLean.CmpArithmetic.V1.full_extract,Sail.BitVec.zeroExtend,BitVec.zeroExtend,BitVec.length,
    Sail.BitVec.length,Int.toNatChecked,Sail.Int.toNatChecked,
    CompiledLean.CmpArithmetic.V1.ex4n,CompiledLean.CmpArithmetic.V1.ex4z,
    CompiledLean.CmpArithmetic.V1.ex4c,CompiledLean.CmpArithmetic.V1.ex4v]
  all_goals try simp [extract64,BitVec.toNat_setWidth]
  all_goals try rw [extract64]
  all_goals repeat first | rw [extract64] | rw [shift_nat]
  all_goals try simp only [Int.add_zero]
  all_goals simp [BitVec.toNat_shiftLeft]
  all_goals rfl

open ArmCertValue
theorem flags_to_core (x y : BitVec 64) :
    ((Sail.BitVec.extractLsb (Math.nzcv x y 0#1) 3 3).setWidth 64,
     (Sail.BitVec.extractLsb (Math.nzcv x y 0#1) 2 2).setWidth 64,
     (Sail.BitVec.extractLsb (Math.nzcv x y 0#1) 1 1).setWidth 64,
     (Sail.BitVec.extractLsb (Math.nzcv x y 0#1) 0 0).setWidth 64) =
    (Op.add3N.eval [x,y,0#64], Op.add3Z.eval [x,y,0#64],
     Op.carry3.eval [x,y,0#64], Op.ovf3.eval [x,y,0#64]) := by
  unfold Math.nzcv CompiledLean.CmpArithmetic.V1.nzcv
  dsimp only
  simp only [CompiledLean.CmpArithmetic.V1.result_eq,
    CompiledLean.CmpArithmetic.V1.ex4n,CompiledLean.CmpArithmetic.V1.ex4z,
    CompiledLean.CmpArithmetic.V1.ex4c,CompiledLean.CmpArithmetic.V1.ex4v,
    CompiledLean.CmpArithmetic.V1.nflag,CompiledLean.CmpArithmetic.V1.zflag,
    CompiledLean.CmpArithmetic.V1.cflag,CompiledLean.CmpArithmetic.V1.vflag,
    CompiledLean.CmpArithmetic.V1.b01_ofBool,CompiledLean.CmpArithmetic.V1.b01_ite]
  rfl

#print axioms shape
#print axioms flags_to_core
end N1D226.AddsShift64Generic.AddShape
