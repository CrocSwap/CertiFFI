import TranslateSpan.ExprOfVHold
import N1D226.CsinvCs64Generic.Value
import N1D226.CsnegCs64Generic.Value
import N1D226.Extr64Generic.Value

open ArmCertValue ArmBridge.Draft
open HeapV2StepCerts.RegBind (rk)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false
namespace TranslateSpan.ConditionalExprCuts

theorem conditional_value (cc : BitVec 4) (n z c v a b : BitVec 64) :
    Op.eval (.cselc cc) [n,z,c,v,a,b] =
      Op.eval .csel [Op.eval (.cond cc) [n,z,c,v],a,b] := by
  change (if condHolds cc n z c v then a else b) =
    (if b01 (condHolds cc n z c v) ≠ 0 then a else b)
  cases choice : condHolds cc n z c v <;> simp [choice,b01]

theorem csinv_outputs (source fin : NativeState) (Rd Rn Rm : BitVec 5)
    (holds : VHolds (N1D226.CsinvCs64Generic.Value.upd source Rd Rn Rm) none source fin) :
    Expr.OutputHolds [(.reg (.x (rk Rd)),
      Expr.csinv 2#4 (.reg (.x (rk Rn))) (.reg (.x (rk Rm))))] source fin := by
  refine ExprOfVHold.reg_output source fin (.x (rk Rd)) _ _ ?_ holds
  exact conditional_value 2#4 (srcVal source (.flag 0)) (srcVal source (.flag 1))
    (srcVal source (.flag 2)) (srcVal source (.flag 3))
    (srcVal source (.reg (.x (rk Rn)))) (~~~srcVal source (.reg (.x (rk Rm))))

theorem csneg_outputs (source fin : NativeState) (Rd Rn Rm : BitVec 5)
    (holds : VHolds (N1D226.CsnegCs64Generic.Value.upd source Rd Rn Rm) none source fin) :
    Expr.OutputHolds [(.reg (.x (rk Rd)),
      Expr.csneg 2#4 (.reg (.x (rk Rn))) (.reg (.x (rk Rm))))] source fin := by
  refine ExprOfVHold.reg_output source fin (.x (rk Rd)) _ _ ?_ holds
  exact conditional_value 2#4 (srcVal source (.flag 0)) (srcVal source (.flag 1))
    (srcVal source (.flag 2)) (srcVal source (.flag 3))
    (srcVal source (.reg (.x (rk Rn)))) (0#64 - srcVal source (.reg (.x (rk Rm))))

theorem extr_outputs (source fin : NativeState) (Rd Rn : BitVec 5) (imms : BitVec 6) (Rm : BitVec 5)
    (holds : VHolds (N1D226.Extr64Generic.Value.upd source Rd Rn imms Rm) none source fin) :
    Expr.OutputHolds [(.reg (.x (rk Rd)),
      Expr.extr imms.toNat (.reg (.x (rk Rn))) (.reg (.x (rk Rm))))] source fin := by
  refine ExprOfVHold.reg_output source fin (.x (rk Rd)) _ _ ?_ holds
  exact BitVec.or_comm _ _

#print axioms csinv_outputs
#print axioms csneg_outputs
#print axioms extr_outputs
end TranslateSpan.ConditionalExprCuts
