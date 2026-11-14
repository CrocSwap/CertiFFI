-- H-P1: Release.Functional from the value layer (certiffi). The remaining inputs are explicit:
-- hsteps/hinv: the per-step value facts (memory stepV_k + stepV_k) and the step invariant
--                 along the body run (I4 from e17_general);
--   hI / hIe    : the 32 input bytes at body entry σ7 and at the caller entry e (shim s0..s6 does not write I);
--   hOut / hx0  : the epilogue s7..s10 leaves the output buffer and x0 (scrubbed to 0 at 364) unchanged.
import ArmCertValue.Bridges
import ArmCertValue.Glue
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
set_option autoImplicit false
namespace ArmCertValue.HeapV2Plan
open ArmCertValue CertiFFI.Prog.Generic.ModelRunView
open HeapV2StepCerts.RegBind (Reg St regVal)
open ArmBridge.Draft ArmCert.Translate ArmCert.Translate.Model

theorem functional_of_value (real : Type) [Sail.SailReal real] (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins) (e : NativeState) (Inv : Nat → NativeState → Prop)
    (hpinO : HeapV2E17.pin pins 1 = pins.x0)
    (hcoh : RegionCoherent mapping (HeapV2E17.pin pins))
    (hinv : ∀ k, k < plan.length → Inv k (stateAt real (stateAt real e 7) k))
    (hsteps : ∀ k (h : k < plan.length), StepFact real Inv mapping (HeapV2E17.pin pins) regions plan k h)
    (bytes : Nat → BitVec 8)
    (hI : ∀ j, j < 32 → regionByte mapping (HeapV2E17.pin pins) (stateAt real e 7) I j = some (bytes j))
    (hIe : ∀ j, j < 32 → ArmBridge.CruxGenGuarded.Release.bufByte mapping e pins.x1 j = some (bytes j))
    (hOut : ∀ i, i < 32 → ArmBridge.CruxGenGuarded.Release.bufByte mapping (stateAt real e 369) pins.x0 i =
      ArmBridge.CruxGenGuarded.Release.bufByte mapping (stateAt real e 364) pins.x0 i)
    (hx0 : (stateAt real e 369).regs.gpr[0] = 0#64) :
    ArmBridge.CruxGenGuarded.Release.Functional mapping pins e (stateAt real e 369) := by
  have hplan := planHolds_of_steps real Inv mapping (HeapV2E17.pin pins) regions plan (stateAt real e 7) hinv hsteps
  have hA0 := agrees_σ0 mapping (HeapV2E17.pin pins) (stateAt real e 7) bytes hI
  have h := hp1_run mapping (HeapV2E17.pin pins) (stateAt real (stateAt real e 7)) (mkInputs (stateAt real e 7) bytes)
    (mkInputs_length _ _) (mkInputs_bytes _ _) hcoh hA0 hplan
  have hval := inVal_mkInputs mapping pins (stateAt real e 7) e bytes hIe
  refine ⟨hx0, ?_⟩
  intro i hi
  rw [hOut i hi, show (364 : Nat) = 7 + 357 from rfl, ArmBridge.CruxGenGuarded.Release.body_index,
    ← hpinO, ← regionByte_eq_bufByte mapping (HeapV2E17.pin pins) _ 1 4 i]
  rw [show (⟨1, 0, 4⟩ : Region) = O from rfl, h i hi, hval, p256k1_eq]

#print axioms functional_of_value

end ArmCertValue.HeapV2Plan
