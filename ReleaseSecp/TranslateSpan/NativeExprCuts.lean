import TranslateSpan.ExprOfVHold
import N1D226.Madd64Generic.DriverValue
import N1D226.Umaddl64Generic.DriverValue
import N1D226.AddsShift64Generic.Value

open ArmCertValue
open ArmBridge.Draft
open HeapV2StepCerts.RegBind (rk)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false

namespace TranslateSpan.NativeExprCuts

theorem madd_outputs (source fin : NativeState) (Rd Rn Ra Rm : BitVec 5)
    (holds : VHolds (N1D226.Madd64Generic.DriverValue.upd source Rd Rn Ra Rm) none source fin) :
    Expr.OutputHolds [(.reg (.x (rk Rd)),
      Expr.madd (.reg (.x (rk Rn))) (.reg (.x (rk Rm))) (.reg (.x (rk Ra))))] source fin := by
  refine ExprOfVHold.reg_output source fin (.x (rk Rd)) _ _ ?_ holds
  change Expr.eval (srcVal source) (N1D226.Madd64Generic.ExprValue.term Rn Ra Rm) ||| 0#64 = _
  rw [BitVec.or_zero]
  rfl

theorem umaddl_outputs (source fin : NativeState) (Rd Rn Rm : BitVec 5)
    (holds : VHolds (N1D226.Umaddl64Generic.DriverValue.upd source Rd Rn Rm) none source fin) :
    Expr.OutputHolds [(.reg (.x (rk Rd)),
      Expr.umaddl (.reg (.x (rk Rn))) (.reg (.x (rk Rm))) (.lit 0#64))] source fin := by
  refine ExprOfVHold.reg_output source fin (.x (rk Rd)) _ _ ?_ holds
  change Expr.eval (srcVal source) (N1D226.Umaddl64Generic.ExprValue.term Rn Rm) ||| 0#64 =
    Expr.eval (srcVal source) (N1D226.Umaddl64Generic.ExprValue.term Rn Rm) + 0#64
  rw [BitVec.or_zero, BitVec.add_zero]

def adds_step (Rd Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) : G.Step :=
  .regFlags (.x (rk Rd))
    (Expr.addsShift .add3 imm6.toNat (.reg (.x (rk Rn))) (.reg (.x (rk Rm))))
    (Expr.addsShift .add3N imm6.toNat (.reg (.x (rk Rn))) (.reg (.x (rk Rm))))
    (Expr.addsShift .add3Z imm6.toNat (.reg (.x (rk Rn))) (.reg (.x (rk Rm))))
    (Expr.addsShift .carry3 imm6.toNat (.reg (.x (rk Rn))) (.reg (.x (rk Rm))))
    (Expr.addsShift .ovf3 imm6.toNat (.reg (.x (rk Rn))) (.reg (.x (rk Rm))))

theorem adds_outputs (source fin : NativeState) (Rd Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5)
    (holds : VHolds (N1D226.AddsShift64Generic.Value.upd source Rd Rn imm6 Rm)
      (N1D226.AddsShift64Generic.Value.flag_updates source Rn imm6 Rm) source fin) :
    Expr.OutputHolds (G.outputs (adds_step Rd Rn imm6 Rm)) source fin := by
  let args := N1D226.AddsShift64Generic.Value.args source Rn imm6 Rm
  refine ExprOfVHold.reg_flags_output source fin (.x (rk Rd))
    ⟨.add3,args⟩ ⟨.add3N,args⟩ ⟨.add3Z,args⟩ ⟨.carry3,args⟩ ⟨.ovf3,args⟩
    _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ holds
  all_goals rfl

#print axioms madd_outputs
#print axioms umaddl_outputs
#print axioms adds_outputs

end TranslateSpan.NativeExprCuts
