-- Memory (certiffi (c2), body classes): register effects of the non-memory classes as
-- RegBind.Holds, from `expected` post-registers (b1 adapters / b2 effects).
import HeapV2StepCerts.MemHolds
import Bridge.CruxGenGuarded.EntryBodyTails
import Bridge.CruxGenGuarded.EntryUmulhTails
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace HeapV2StepCerts.RegBind
open ArmBridge.Draft

/-! ### Generic single-write Holds -/

theorem holds_drop1 (x y : NativeState) (R : Fin 31) (v : BitVec 64)
    (gpr : y.regs.gpr = x.regs.gpr.set R.val v R.isLt) (sp : y.regs.SP_EL0 = x.regs.SP_EL0) :
    Holds [(.x R, .drop)] x y := by
  intro r
  cases r with
  | sp => simp [updOf, List.find?, regVal, sp]
  | x j =>
    by_cases h : R = j
    · subst h; simp [updOf, List.find?]
    · have e : (Reg.x R = Reg.x j) = False := by simp [h]
      simp only [updOf, List.find?, e, decide_false, Option.map_none, Option.getD_none]
      simp only [regVal, gpr, Vector.getElem_set, Fin.val_inj]
      simp [h]

theorem holds_set1 (x y : NativeState) (R : Fin 31) (src : Reg) (c : Int) (v : BitVec 64)
    (gpr : y.regs.gpr = x.regs.gpr.set R.val v R.isLt) (sp : y.regs.SP_EL0 = x.regs.SP_EL0)
    (hv : v = regVal x src + BitVec.ofInt 64 c) :
    Holds [(.x R, .set src c)] x y := by
  intro r
  cases r with
  | sp => simp [updOf, List.find?, regVal, sp]
  | x j =>
    by_cases h : R = j
    · subst h
      simp only [updOf, List.find?, decide_true, Option.map_some, Option.getD_some]
      simp [regVal, gpr, hv]
    · have e : (Reg.x R = Reg.x j) = False := by simp [h]
      simp only [updOf, List.find?, e, decide_false, Option.map_none, Option.getD_none]
      simp only [regVal, gpr, Vector.getElem_set, Fin.val_inj]
      simp [h]

theorem holds_sp (x y : NativeState) (c : Int) (gpr : y.regs.gpr = x.regs.gpr)
    (sp : y.regs.SP_EL0 = x.regs.SP_EL0 + BitVec.ofInt 64 c) : Holds [(.sp, .set .sp c)] x y := by
  intro r
  cases r with
  | sp => simp [updOf, List.find?, regVal, sp]
  | x j => simp [updOf, List.find?, regVal, gpr]

/-! ### Width-64 integer_subrange arithmetic (Awc.sres_toNat pattern) -/

theorem subrange64_toNat (n : Int) :
    (Sail.BitVec.zeroExtend (BitVec.castWidth (m := 64)
      (Functions.integer_subrange n (↑(Int.toNatChecked 64) - 1) 0)) 64).toNat = (n % 2 ^ 64).toNat := by
  unfold Functions.integer_subrange
  simp [Sail.BitVec.zeroExtend, BitVec.castWidth, Sail.get_slice_int, Int.toNatChecked, BitVec.extractLsb',
    BitVec.toNat_ofInt]
  omega

@[simp] theorem pstate_set_sp (v : ProcState) (r : Regs) : (Register.PSTATE.set v r).SP_EL0 = r.SP_EL0 := rfl
@[simp] theorem pstate_set_gpr (v : ProcState) (r : Regs) : (Register.PSTATE.set v r).gpr = r.gpr := rfl

theorem shl0 (v : BitVec 64) : (BitVec.extractLsb 63 0 v <<< (0 : Nat)).toNat = v.toNat := by
  simp only [BitVec.shiftLeft_zero, BitVec.extractLsb_toNat, Nat.shiftRight_zero]; omega

#print axioms holds_drop1
#print axioms holds_set1
#print axioms holds_sp
#print axioms subrange64_toNat
end HeapV2StepCerts.RegBind
