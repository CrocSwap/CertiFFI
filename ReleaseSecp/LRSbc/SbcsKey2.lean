import ArmCertValueTail.Flags
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxRecDepth 1000000
namespace LRSbc.SbcsKey2
set_option maxHeartbeats 4000000 in
drive_spec native, complete :
  fun (s : SequentialState Regs oracleChoiceSource) (Rd Rn Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (el : s.regs.PSTATE.EL = 0#2) (a64 : s.regs.PSTATE.nRW = 0#1) (aa64 : s.regs.FeatureImpl[4]! = true) (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) =>
    ((do let _ ← (decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 1#1 1#1 : SailM Unit)
         let u ← get
         pure (u.regs.gpr, u.regs.SP_EL0, u.regs.PSTATE.N, u.regs.PSTATE.Z, u.regs.PSTATE.C, u.regs.PSTATE.V)) : SailM _) s
theorem k2a (x : BitVec 64) (c : BitVec 1) : (x + ~~~0#64 + c.setWidth 64).toNat = (x.toNat + 18446744073709551615 + c.toNat) % 18446744073709551616 := by
  have := c.isLt
  rw [BitVec.not_zero, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_allOnes, BitVec.toNat_setWidth]
  omega
theorem k3 (x : BitVec 64) (c : BitVec 1) :
    (Sail.BitVec.zeroExtend (BitVec.castWidth (m := 64) (integer_subrange ((x.toNat : Int) + 18446744073709551615 + (c.toNat : Int)) 63 0)) 64).toNat
      = (x.toNat + 18446744073709551615 + c.toNat) % 18446744073709551616 := by
  have := c.isLt; have := x.isLt
  simp [Functions.integer_subrange, Sail.BitVec.zeroExtend, BitVec.castWidth, Sail.get_slice_int, Int.toNatChecked,
    BitVec.extractLsb', BitVec.toNat_ofInt, Sail.BitVec.extractLsb, BitVec.extractLsb, Sail.Int.toNatChecked]
  omega
theorem val2 (x : BitVec 64) (c : BitVec 1) :
    Sail.BitVec.zeroExtend (BitVec.castWidth (m := 64) (integer_subrange ((x.toNat : Int) + 18446744073709551615 + (c.toNat : Int)) 63 0)) 64
      = x + ~~~0#64 + c.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [k3 x c, k2a x c]

theorem iteTT {α : Sort _} (a b : α) : (if true = true then a else b) = a := rfl

theorem gval (x y : BitVec 64) (c : BitVec 1) :
    Sail.BitVec.zeroExtend (BitVec.castWidth (m := 64) (integer_subrange ((x.toNat : Int) + ((18446744073709551615 - y.toNat : Nat) : Int) + (c.toNat : Int)) 63 0)) 64
      = x + ~~~y + c.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  have := c.isLt; have := x.isLt; have := y.isLt
  simp [Functions.integer_subrange, Sail.BitVec.zeroExtend, BitVec.castWidth, Sail.get_slice_int, Int.toNatChecked,
    BitVec.extractLsb', BitVec.toNat_ofInt, Sail.BitVec.extractLsb, BitVec.extractLsb, Sail.Int.toNatChecked,
    BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_setWidth]
  omega

open HeapV2StepCerts.RegRoots HeapV2StepCerts.FlagRoots HeapV2StepCerts.FlagRoots.TstF4 ArmCertValue.Flags in
set_option maxHeartbeats 4000000 in
theorem key_rm (s : ArmBridge.Draft.NativeState) (Rd Rn Rm : BitVec 5) (hRd : ¬ (Rd.toNat : Int) = 31) (hRn : ¬ (Rn.toNat : Int) = 31)
    (y : BitVec 64) (hY : (if (Rm.toNat : Int) = 31 then 0#64 else BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb s.regs.gpr[(GPRSummary.key Rm.toNat).val] (Int.toNatChecked 63) 0)) = y) :
    ∃ u, native s Rd Rn Rm = .ok
      (s.regs.gpr.set (GPRSummary.key Rd.toNat).val (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + ~~~y + s.regs.PSTATE.C.setWidth 64) (GPRSummary.key Rd.toNat).isLt,
       s.regs.SP_EL0, BitVec.ofBool (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + ~~~y + s.regs.PSTATE.C.setWidth 64).msb, (if (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + ~~~y + s.regs.PSTATE.C.setWidth 64) = 0#64 then 1#1 else 0#1),
       (if 2 ^ 64 ≤ s.regs.gpr[(GPRSummary.key Rn.toNat).val].toNat + (~~~y).toNat + s.regs.PSTATE.C.toNat then 1#1 else 0#1),
       (if s.regs.gpr[(GPRSummary.key Rn.toNat).val].toInt + (~~~y).toInt + s.regs.PSTATE.C.toNat < -2 ^ 63 ∨ 2 ^ 63 ≤ s.regs.gpr[(GPRSummary.key Rn.toNat).val].toInt + (~~~y).toInt + s.regs.PSTATE.C.toNat then 1#1 else 0#1)) u := by
  unfold native
  simp only [hRd, hRn, ite_true, ite_false, dite_eq_ite, ite_self, Bool.false_eq_true, pstate_set_sp, pstate_set_gpr, sp_set_gpr, ArmFull.Register.PSTATE_set]
  simp only [hY, iteTT]
  apply ok_congr
  generalize s.regs.gpr[(GPRSummary.key Rn.toNat).val] = x
  generalize s.regs.PSTATE.C = c
  have hx : (BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb x (Int.toNatChecked 63) 0)) = x := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.castWidth, Sail.BitVec.extractLsb, BitVec.extractLsb, Int.toNatChecked]
  have hR : (BitVec.castWidth (m := 64) (integer_subrange ((x.toNat : Int) + (~~~y).toNat + c.toNat) ((64 : Nat) - 1) 0)) = x + ~~~y + c.setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp [Functions.integer_subrange, BitVec.castWidth, Sail.get_slice_int, BitVec.extractLsb', BitVec.toNat_ofInt,
      BitVec.toNat_add, BitVec.toNat_setWidth, Sail.Int.toNatChecked, Int.toNatChecked, BitVec.toNat_ofNat]
    omega
  simp only [hx, Bool.false_eq_true, ite_false, BitVec.length]
  simp only [Prod.mk.injEq, hR, gval, (ex4 _ _ _ _).1, (ex4 _ _ _ _).2.1, (ex4 _ _ _ _).2.2.1, (ex4 _ _ _ _).2.2.2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · trivial
  · trivial
  · have hxN : (BitVec.castWidth (n := Int.toNatChecked 63 + 1) (m := 64) (Sail.BitVec.extractLsb x (Int.toNatChecked 63) 0)) = x := hx
    have hYN : (if (Rm.toNat : Int) = 31 then 0#64 else BitVec.castWidth (n := Int.toNatChecked 63 + 1) (m := 64)
        (Sail.BitVec.extractLsb s.regs.gpr[(GPRSummary.key Rm.toNat).val] (Int.toNatChecked 63) 0)) = y := hY
    rw [hxN, hYN]
    have hRN : (BitVec.castWidth (n := Int.toNatChecked ((((64 : Nat) : Int) - 1) - 0 + 1)) (m := 64)
        (integer_subrange ((x.toNat : Int) + (~~~y).toNat + c.toNat) (((64 : Nat) : Int) - 1) 0)) = x + ~~~y + c.setWidth 64 := hR
    rw [hRN]
    exact nflag _
  · exact zflag _
  · exact cflag x (~~~y) c
  · exact vflag x (~~~y) c

open HeapV2StepCerts.RegRoots HeapV2StepCerts.FlagRoots in
/-- SBCS Xd, Xn, XZR (heap-v2 rows): the projected root's values. -/
theorem key (s : ArmBridge.Draft.NativeState) (Rd Rn : BitVec 5) (hRd : ¬ (Rd.toNat : Int) = 31) (hRn : ¬ (Rn.toNat : Int) = 31) :
    ∃ u, native s Rd Rn 31#5 = .ok
      (s.regs.gpr.set (GPRSummary.key Rd.toNat).val (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + ~~~0#64 + s.regs.PSTATE.C.setWidth 64) (GPRSummary.key Rd.toNat).isLt,
       s.regs.SP_EL0, BitVec.ofBool (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + ~~~0#64 + s.regs.PSTATE.C.setWidth 64).msb, (if (s.regs.gpr[(GPRSummary.key Rn.toNat).val] + ~~~0#64 + s.regs.PSTATE.C.setWidth 64) = 0#64 then 1#1 else 0#1),
       (if 2 ^ 64 ≤ s.regs.gpr[(GPRSummary.key Rn.toNat).val].toNat + (~~~0#64).toNat + s.regs.PSTATE.C.toNat then 1#1 else 0#1),
       (if s.regs.gpr[(GPRSummary.key Rn.toNat).val].toInt + (~~~0#64).toInt + s.regs.PSTATE.C.toNat < -2 ^ 63 ∨ 2 ^ 63 ≤ s.regs.gpr[(GPRSummary.key Rn.toNat).val].toInt + (~~~0#64).toInt + s.regs.PSTATE.C.toNat then 1#1 else 0#1)) u :=
  key_rm s Rd Rn 31#5 hRd hRn 0#64 (if_pos (by decide))

#print axioms key
end LRSbc.SbcsKey2
