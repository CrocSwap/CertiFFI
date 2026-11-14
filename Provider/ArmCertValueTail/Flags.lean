-- ArmCertValueTail.Flags: Sail AddWithCarry flag bits (as drive_spec leaves them) =
-- the Core v4 flag ops (add3N/add3Z/carry3/ovf3), plus a flag-setting single-write VHolds.
import ArmCertValueTail.Def
import HeapV2StepCerts.FlagRootsNZCV
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxRecDepth 1000000
namespace ArmCertValue.Flags
open HeapV2StepCerts.RegBind (Reg regVal)

theorem bv1 (a : BitVec 1) : a = 0#1 ∨ a = 1#1 := by
  rcases a with ⟨⟨n, hn⟩⟩
  have : n = 0 ∨ n = 1 := by omega
  rcases this with rfl | rfl
  · left; rfl
  · right; rfl

theorem ex4 (a b c d : BitVec 1) :
    Sail.BitVec.extractLsb (a ++ b ++ c ++ d) 3 3 = a ∧ Sail.BitVec.extractLsb (a ++ b ++ c ++ d) 2 2 = b ∧
    Sail.BitVec.extractLsb (a ++ b ++ c ++ d) 1 1 = c ∧ Sail.BitVec.extractLsb (a ++ b ++ c ++ d) 0 0 = d := by
  rcases bv1 a with rfl | rfl <;> rcases bv1 b with rfl | rfl <;>
    rcases bv1 c with rfl | rfl <;> rcases bv1 d with rfl | rfl <;> decide

theorem iteFF {α : Sort _} (a b : α) : (if false = true then a else b) = b := rfl

theorem nflag (r : BitVec 64) :
    BitVec.setWidth 1 (BitVec.join1 [BitVec.access r (Int.toNatChecked ((64 : Nat) - 1))]) = BitVec.ofBool r.msb := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have : i = 0 := by omega
  subst this
  simp [BitVec.join1, BitVec.access, Int.toNatChecked, BitVec.msb_eq_getLsbD_last]
  rw [getElem!_pos r 63 (by omega)]
  generalize r[63] = b
  cases b <;> rfl

theorem zflag (r : BitVec 64) : (if IsZero r = true then 1#1 else 0#1) = if r = 0#64 then 1#1 else 0#1 := by
  simp [IsZero, Sail.BitVec.length, Sail.BitVec.castWidth]

theorem cflag (x y : BitVec 64) (c : BitVec 1) :
    (if ((((x + y + c.setWidth 64).toNat : Nat) : Int) == (x.toNat : Int) + y.toNat + c.toNat) = true then 0#1 else 1#1) =
      if 2 ^ 64 ≤ x.toNat + y.toNat + c.toNat then 1#1 else 0#1 := by
  have hc : c.toNat < 2 := c.isLt
  by_cases h : 2 ^ 64 ≤ x.toNat + y.toNat + c.toNat
  · rw [if_pos h, if_neg]; simp [BitVec.toNat_add, BitVec.toNat_setWidth]; omega
  · rw [if_neg h, if_pos]; simp [BitVec.toNat_add, BitVec.toNat_setWidth]; omega

theorem vflag (x y : BitVec 64) (c : BitVec 1) :
    (if ((x + y + c.setWidth 64).toInt == x.toInt + y.toInt + c.toNat) = true then 0#1 else 1#1) =
      if x.toInt + y.toInt + c.toNat < -2 ^ 63 ∨ 2 ^ 63 ≤ x.toInt + y.toInt + c.toNat then 1#1 else 0#1 := by
  have hc : c.toNat < 2 := c.isLt
  have ht : (x + y + c.setWidth 64).toInt = (x.toInt + y.toInt + (c.toNat : Int)).bmod (2 ^ 64) := by
    rw [BitVec.toInt_add, BitVec.toInt_add, BitVec.toInt_setWidth, Int.bmod_add_bmod, Int.add_bmod_bmod]
  have hx1 := BitVec.le_toInt x
  have hx2 := BitVec.toInt_lt (x := x)
  have hy1 := BitVec.le_toInt y
  have hy2 := BitVec.toInt_lt (x := y)
  rw [ht, Int.bmod_def]
  simp only [beq_iff_eq]
  simp at hx1 hx2 hy1 hy2
  split <;> split <;> split <;> first | rfl | (exfalso; omega)

theorem b01_ofBool (b : Bool) : (BitVec.ofBool b).setWidth 64 = b01 b := by cases b <;> rfl
theorem b01_ite (p : Prop) [Decidable p] : (if p then 1#1 else 0#1).setWidth 64 = b01 (decide p) := by
  by_cases h : p <;> simp [h, b01]
theorem toNat_c64 (c : BitVec 1) : (c.setWidth 64).toNat = c.toNat := by
  have := c.isLt; simp [BitVec.toNat_setWidth]; omega

/-- One GPR written and NZCV set, everything else (other GPRs, SP) unchanged. -/
theorem vholds_set1_fl (x y : ArmBridge.Draft.NativeState) (R : Fin 31) (u : VUpd) (v : BitVec 64)
    (n z c vv : VUpd)
    (gpr : y.regs.gpr = x.regs.gpr.set R.val v R.isLt) (sp : y.regs.SP_EL0 = x.regs.SP_EL0)
    (hv : v = u.eval x) (h0 : flagWord y 0 = n.eval x) (h1 : flagWord y 1 = z.eval x)
    (h2 : flagWord y 2 = c.eval x) (h3 : flagWord y 3 = vv.eval x) :
    VHolds [(.x R, some u)] (some (n, z, c, vv)) x y := by
  refine ⟨fun r => ?_, h0, h1, h2, h3⟩
  cases r with
  | sp => simp [List.find?, regVal, sp]
  | x j =>
    by_cases h : R = j
    · subst h; simp [List.find?, regVal, gpr, hv]
    · have e : (Reg.x R = Reg.x j) = False := by simp [h]
      simp only [List.find?, e, decide_false, Option.map_none]
      simp only [regVal, gpr, Vector.getElem_set, Fin.val_inj]
      simp [h]

end ArmCertValue.Flags
