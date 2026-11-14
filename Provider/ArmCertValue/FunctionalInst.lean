-- H-P1 instantiated on the release run (certiffi): Release.Functional from
--   * DeploymentPremises at body entry σ7 (I4 invariant via e17_general; x0 scrub via ct2Residue_full),
-- * the per-step value facts (hsteps: stepV_k for class steps, memory stepV_k for memory steps,
-- branch steps; currently delivered for most k, the rest stay this hypothesis),
-- * input presence at σ7 and the shim frame facts (ShimFrameV).
import ArmCertValue.Functional
import ArmCertValueMem.Coherent
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
set_option autoImplicit false
namespace ArmCertValue.HeapV2Plan
open ArmCertValue CertiFFI.Prog.Generic.ModelRunView
open HeapV2StepCerts.RegBind (Reg St regVal)
open ArmBridge.Draft ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.CruxGenGuarded HeapV2StepCerts.E17General

theorem functional_inst (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (e : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins (stateAt real e 7) budget) (hb : 357 ≤ budget)
    (hsteps : ∀ k (h : k < plan.length),
      StepFact real (I4 spec config rows mapping base pins (stateAt real e 7) budget) mapping (HeapV2E17.pin pins)
        regions plan k h)
    (hpres : ∀ j, j < 32 → ∃ b, Release.bufByte mapping (stateAt real e 7) pins.x1 j = some b)
    (inUnch : ∀ j, j < 32 → Release.bufByte mapping (stateAt real e 7) pins.x1 j = Release.bufByte mapping e pins.x1 j)
    (outUnch : ∀ i, i < 32 → Release.bufByte mapping (stateAt real e 369) pins.x0 i =
      Release.bufByte mapping (stateAt real e 364) pins.x0 i)
    (x0Out : (stateAt real e 369).regs.gpr[0] = (stateAt real e 364).regs.gpr[0]) :
    Release.Functional mapping pins e (stateAt real e 369) := by
  have hE := (e17_general real spec config rows mapping base pins (stateAt real e 7) budget dp hb).1
  have hinv : ∀ k, k < plan.length → I4 spec config rows mapping base pins (stateAt real e 7) budget k
      (stateAt real (stateAt real e 7) k) := by
    intro k hk
    rw [plan_length] at hk
    exact (hE k (by omega)).1
  let bytes : Nat → BitVec 8 := fun j => (Release.bufByte mapping (stateAt real e 7) pins.x1 j).getD 0#8
  have hσ : ∀ j, j < 32 → Release.bufByte mapping (stateAt real e 7) pins.x1 j = some (bytes j) := by
    intro j hj
    obtain ⟨b, hb'⟩ := hpres j hj
    simp only [bytes, hb', Option.getD_some]
  have hI : ∀ j, j < 32 → regionByte mapping (HeapV2E17.pin pins) (stateAt real e 7) I j = some (bytes j) := by
    intro j hj
    rw [show I = (⟨2, 0, 4⟩ : Region) from rfl, regionByte_eq_bufByte]
    exact hσ j hj
  have hIe : ∀ j, j < 32 → Release.bufByte mapping e pins.x1 j = some (bytes j) := by
    intro j hj
    rw [← inUnch j hj]; exact hσ j hj
  have hZ := HeapV2StepCerts.ZSteps.ct2Residue_full real spec config rows mapping base pins (stateAt real e 7) budget dp hb
  have hx0 : (stateAt real e 369).regs.gpr[0] = 0#64 := by
    rw [x0Out, show (364 : Nat) = 7 + 357 from rfl, Release.body_index]
    exact hZ.2.2.2.2.2.2.1 ⟨0, by decide⟩
  exact functional_of_value real mapping pins e _ rfl (ArmCertValue.MemRegion.regionCoherent mapping _) hinv hsteps
    bytes hI hIe outUnch hx0

#print axioms functional_inst

end ArmCertValue.HeapV2Plan
