-- Shared value facts used to bind a final RET to its original input register.
import ArmCertValue.PhysicalSSA
open Sail ArmFull ArmCertValue
set_option autoImplicit false
namespace ArmCertPipe.ReturnValues

theorem low_of_value (x : HeapV2StepCerts.RegBind.St) (r : Fin 31) (value : BitVec 64)
    (same : HeapV2StepCerts.RegBind.regVal x (.x r) = value) (low : value.toNat < 2 ^ 55) :
    (x.regs.gpr[r.val]).toNat < 2 ^ 55 := by
  change (HeapV2StepCerts.RegBind.regVal x (.x r)).toNat < 2 ^ 55
  rw [same]
  exact low

/-- Appending definitions leaves every original input entry unchanged. -/
theorem input_prefix : ∀ (ds : List Def) (vals : List (BitVec 64)) (i : Nat),
    i < vals.length → (extend vals ds).getD i 0 = vals.getD i 0
  | [], _, _, _ => rfl
  | d :: ds, vals, i, h => by
    show (extend (vals ++ [d.eval vals]) ds).getD i 0 = _
    rw [input_prefix ds (vals ++ [d.eval vals]) i (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

#print axioms low_of_value
#print axioms input_prefix
end ArmCertPipe.ReturnValues
