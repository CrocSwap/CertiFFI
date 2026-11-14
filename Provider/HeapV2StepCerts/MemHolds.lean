-- Memory ((c2)): register effects of the memory classes as RegBind.Holds,
-- from the class post-states (ldrbPost / strbPost / ldpPost; Stp/Stp8 leave registers).
import HeapV2StepCerts.RegBindCore
import ArmCertWalk.MemClassLdrb
import ArmCertWalk.MemClassStrb
import ArmCertWalk.MemClassLdp
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
namespace HeapV2StepCerts.RegBind
open ArmBridge.Draft

theorem key_val : ∀ n < 31, (GPRSummary.key n).val = n := by decide

def rk (R : BitVec 5) : Fin 31 := GPRSummary.key R.toNat

/-- Ldrb post-index: Rn += sext imm9, Rt := loaded byte. -/
def updLdrb (Rn Rt : BitVec 5) (imm9 : BitVec 9) : List (Reg × Upd) :=
  [(.x (rk Rn), .set (.x (rk Rn)) imm9.toInt), (.x (rk Rt), .drop)]
/-- Strb post-index: Rn += sext imm9. -/
def updStrb (Rn : BitVec 5) (imm9 : BitVec 9) : List (Reg × Upd) :=
  [(.x (rk Rn), .set (.x (rk Rn)) imm9.toInt)]
/-- Ldp/Ldp8: Rt, Rt2 := loaded data. -/
def updLdp (Rt Rt2 : BitVec 5) : List (Reg × Upd) := [(.x (rk Rt), .drop), (.x (rk Rt2), .drop)]

theorem setGpr_get (s : NativeState) (i : Fin 31) (v : BitVec 64) (j : Fin 31) :
    (CryptoMem.MemCore.setGpr s i v).regs.gpr[j.val] = if i = j then v else s.regs.gpr[j.val] := by
  unfold CryptoMem.MemCore.setGpr
  simp only [Vector.getElem_set, Fin.val_inj]

theorem setGpr_sp (s : NativeState) (i : Fin 31) (v : BitVec 64) :
    (CryptoMem.MemCore.setGpr s i v).regs.SP_EL0 = s.regs.SP_EL0 := rfl

theorem sext_ofInt (imm9 : BitVec 9) : sign_extend imm9 64 = BitVec.ofInt 64 imm9.toInt := by
  rfl

theorem holds_ldrb (x y : NativeState) (Rn Rt : BitVec 5) (imm9 : BitVec 9) (v : BitVec 8)
    (hnt : rk Rn ≠ rk Rt)
    (gpr : y.regs.gpr = (ArmCertMem.LdrbEval.ldrbPost x Rn Rt imm9 v).regs.gpr)
    (sp : y.regs.SP_EL0 = x.regs.SP_EL0) : Holds (updLdrb Rn Rt imm9) x y := by
  intro r
  cases r with
  | sp => simp [updOf, updLdrb, List.find?, regVal, sp]
  | x j =>
    by_cases hn : rk Rn = j
    · subst hn
      simp only [updOf, updLdrb, List.find?, decide_true, Option.map_some, Option.getD_some]
      simp only [regVal, gpr, ArmCertMem.LdrbEval.ldrbPost, setGpr_get, ite_true, rk] at *
      simp [Sail.BitVec.zeroExtend, sext_ofInt]
    · by_cases ht : rk Rt = j
      · subst ht
        have : (Reg.x (rk Rn) = Reg.x (rk Rt)) = False := by simp [hnt]
        simp [updOf, updLdrb, List.find?, this]
      · have h1 : (Reg.x (rk Rn) = Reg.x j) = False := by simp [hn]
        have h2 : (Reg.x (rk Rt) = Reg.x j) = False := by simp [ht]
        simp only [updOf, updLdrb, List.find?, h1, h2, decide_false, Option.map_none, Option.getD_none]
        simp only [regVal, gpr, ArmCertMem.LdrbEval.ldrbPost, setGpr_get, rk] at *
        simp [hn, ht]

theorem holds_strb (x y : NativeState) (Rn : BitVec 5) (imm9 : BitVec 9)
    (gpr : y.regs.gpr = (ArmCertMem.StrbEval.strbPost x Rn imm9).regs.gpr)
    (sp : y.regs.SP_EL0 = x.regs.SP_EL0) : Holds (updStrb Rn imm9) x y := by
  intro r
  cases r with
  | sp => simp [updOf, updStrb, List.find?, regVal, sp]
  | x j =>
    by_cases hn : rk Rn = j
    · subst hn
      simp only [updOf, updStrb, List.find?, decide_true, Option.map_some, Option.getD_some]
      simp only [regVal, gpr, ArmCertMem.StrbEval.strbPost, setGpr_get, ite_true, rk] at *
      simp [Sail.BitVec.zeroExtend, sext_ofInt]
    · have h1 : (Reg.x (rk Rn) = Reg.x j) = False := by simp [hn]
      simp only [updOf, updStrb, List.find?, h1, decide_false, Option.map_none, Option.getD_none]
      simp only [regVal, gpr, ArmCertMem.StrbEval.strbPost, setGpr_get, rk] at *
      simp [hn]

theorem holds_ldp (x y : NativeState) (Rt Rt2 : BitVec 5) (data : BitVec 128)
    (gpr : y.regs.gpr = (ArmCertMem.LdpEval.ldpPost x Rt Rt2 data).regs.gpr)
    (sp : y.regs.SP_EL0 = x.regs.SP_EL0) : Holds (updLdp Rt Rt2) x y := by
  intro r
  cases r with
  | sp => simp [updOf, updLdp, List.find?, regVal, sp]
  | x j =>
    by_cases h1 : rk Rt = j
    · subst h1; simp [updOf, updLdp, List.find?]
    · by_cases h2 : rk Rt2 = j
      · subst h2
        have : (Reg.x (rk Rt) = Reg.x (rk Rt2)) = False := by simp [h1]
        simp [updOf, updLdp, List.find?, this]
      · have e1 : (Reg.x (rk Rt) = Reg.x j) = False := by simp [h1]
        have e2 : (Reg.x (rk Rt2) = Reg.x j) = False := by simp [h2]
        simp only [updOf, updLdp, List.find?, e1, e2, decide_false, Option.map_none, Option.getD_none]
        simp only [regVal, gpr, ArmCertMem.LdpEval.ldpPost, setGpr_get, rk] at *
        simp [h1, h2]

theorem holds_nil (x y : NativeState) (gpr : y.regs.gpr = x.regs.gpr) (sp : y.regs.SP_EL0 = x.regs.SP_EL0) :
    Holds [] x y := by
  intro r
  cases r with
  | sp => simp [updOf, regVal, sp]
  | x j => simp [updOf, regVal, gpr]

#print axioms holds_ldrb
#print axioms holds_strb
#print axioms holds_ldp
#print axioms holds_nil
end HeapV2StepCerts.RegBind
