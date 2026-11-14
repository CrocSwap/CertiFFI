-- Memory: physical bytes of the plan's data accesses (light module for CodeData / MemNextV3).
import ArmCertTranslateModel.HeapV2Plan
import ArmCertTranslateModel.HeapV2E17Table
import ArmCertWalk.MemPair
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
namespace HeapV2StepCerts.MemNext
open ArmCertWalk

/-- Physical bytes of the plan's data accesses (both 8-byte halves of a pair). -/
def dataBytes (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (x : Nat) : Prop :=
  ∃ e ∈ HeapV2Plan.symbolicAccesses, ∃ va n, (va = HeapV2E17.dataVA p e ∨ va = plus8 (HeapV2E17.dataVA p e)) ∧
    mapping va = some n ∧ n ≤ x ∧ x < n + e.2.2.2.1

end HeapV2StepCerts.MemNext
