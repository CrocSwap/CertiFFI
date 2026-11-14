-- Memory (H-P2,): the decided residue tables, split out of Residue.Core so Core stays under the
-- M4096 / 70% watchdog (the kernel decides were Core's peak, not its imports). Light imports only.
import HeapV2StepCerts.RegBindData
import ArmCertTranslateModel.HeapV2Plan
set_option autoImplicit false
set_option maxRecDepth 4096
namespace HeapV2StepCerts.Residue
open HeapV2StepCerts.RegBind ArmCert.Translate.Model

/-- The registers no plan step writes (decided against the upds table below). -/
def frameRegs : List (Fin 31) := [18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]

def frameKeep (k : Nat) : Bool := frameRegs.all fun r => updOf (upds k) (.x r) == .keep

theorem frameKeep_ok_0 : ∀ i < 60, frameKeep (0 + i) = true := by decide +kernel
theorem frameKeep_ok_1 : ∀ i < 60, frameKeep (60 + i) = true := by decide +kernel
theorem frameKeep_ok_2 : ∀ i < 60, frameKeep (120 + i) = true := by decide +kernel
theorem frameKeep_ok_3 : ∀ i < 60, frameKeep (180 + i) = true := by decide +kernel
theorem frameKeep_ok_4 : ∀ i < 60, frameKeep (240 + i) = true := by decide +kernel
theorem frameKeep_ok_5 : ∀ i < 57, frameKeep (300 + i) = true := by decide +kernel

theorem frameKeep_ok (k : Nat) (hk : k < 357) : frameKeep k = true := by
  if h0 : k < 60 then
    have e := frameKeep_ok_0 (k - 0) (by omega); rwa [show 0 + (k - 0) = k by omega] at e
  else if h1 : k < 120 then
    have e := frameKeep_ok_1 (k - 60) (by omega); rwa [show 60 + (k - 60) = k by omega] at e
  else if h2 : k < 180 then
    have e := frameKeep_ok_2 (k - 120) (by omega); rwa [show 120 + (k - 120) = k by omega] at e
  else if h3 : k < 240 then
    have e := frameKeep_ok_3 (k - 180) (by omega); rwa [show 180 + (k - 180) = k by omega] at e
  else if h4 : k < 300 then
    have e := frameKeep_ok_4 (k - 240) (by omega); rwa [show 240 + (k - 240) = k by omega] at e
  else
    have e := frameKeep_ok_5 (k - 300) (by omega); rwa [show 300 + (k - 300) = k by omega] at e

/-- Every store is x0-based (output, pin 1) or SP-based (frame, pin 0). -/
theorem store_pins : ∀ e ∈ HeapV2Plan.symbolicAccesses, e.2.2.2.2 = true → e.2.1 = 0 ∨ e.2.1 = 1 := by decide +kernel

#print axioms frameKeep_ok
#print axioms store_pins
end HeapV2StepCerts.Residue
