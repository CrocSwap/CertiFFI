-- Memory: x1 at the epilogue TST x1 (step 350) is the constant 0 (MOVZ x1, #0 at step 333),
-- carried by ValBind from step 334 on.
import HeapV2StepCerts.ValBind
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
namespace HeapV2StepCerts.ValBind
open HeapV2StepCerts.RegBind ArmBridge.Draft

theorem x1_zero {k : Nat} (hk : ((.x 1 : Reg), 0, (0 : Int)) ∈ vtab k) {q : Inputs} {x : NativeState}
    (vb : ValBind q k x) : regVal x (.x 1) = 0#64 := by
  have h := vb.1 _ hk
  simpa [vpin] using h

/-- at step 350 (TST x1, #7) x1 = 0. -/
theorem x1_at_350 {q : Inputs} {x : NativeState} (vb : ValBind q 350 x) : regVal x (.x 1) = 0#64 :=
  x1_zero (by decide +kernel) vb

/-- x1 = 0 on every state from 334 to 350 (after the MOVZ, through the zeroing block to the TST). -/
theorem x1_range_b : ∀ i < 17, ((.x 1 : Reg), 0, (0 : Int)) ∈ vtab (334 + i) := by decide +kernel
theorem x1_range (k : Nat) (lo : 334 ≤ k) (hi : k ≤ 350) : ((.x 1 : Reg), 0, (0 : Int)) ∈ vtab k := by
  have h := x1_range_b (k - 334) (by omega)
  rwa [show 334 + (k - 334) = k by omega] at h

#print axioms x1_at_350
end HeapV2StepCerts.ValBind
