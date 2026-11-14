-- Memory: the heap-v2 code scope (image offsets of every plan code-word byte), in a light module
-- so Boolean deployment checks (CodeData) need not import the step machinery.
import ArmCertTranslateModel.HeapV2Plan
import ArmCertTranslateModel.HeapV2Image
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
namespace HeapV2StepCerts

/-- The code scope: every byte of every plan code word (image offsets). -/
def codeOffsets : List Nat :=
  HeapV2Plan.codeWords.flatMap fun c => (List.range 4).map fun i => HeapV2.entryOffset + c.1 + i

/-- `CodeHyps.scope` used by the checks. -/
def codeScope : Nat → Prop := (· ∈ codeOffsets)

end HeapV2StepCerts
