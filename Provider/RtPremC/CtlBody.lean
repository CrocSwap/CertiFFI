-- RtPremC.CtlBody (, premise C): ctl/footprint frame across the whole heap-v2 body.
-- (H-P4 (2) groundwork): the heap-v2 body keeps PSTATE.DIT AND writes only the plan's data bytes
-- (MemFrame (dataBytes pins mapping)) on the whole run, including the final RET at k = 357 (to X30):
-- dit_body_mem (∀ k ≤ 357) and dit_body_ret (state 358, the RET's landing, e.g. the shim's s7).
import RtDit.DitBody
import RtPremC.CtlSegM_00
import RtPremC.CtlSegM_01
import RtPremC.CtlSegM_02
import RtPremC.CtlSegM_03
import RtPremC.CtlSegM_04
import RtPremC.CtlSegM_05
import RtPremC.CtlSegM_06
import RtPremC.CtlSegM_07
import RtPremC.CtlSegM_08
import RtPremC.CtlSegM_09
import RtPremC.CtlSegM_10
import RtPremC.CtlSegM_11
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV4 HeapV2StepCerts.E17General
open ArmBridge.Boundary ArmBridge.CruxCore HeapV2StepCerts
open CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false
namespace RtPremC

theorem ctlStepsM (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, k < 357 → RtPremC.CtlStepM real spec config rows mapping base pins entry budget k := by
  intro k hk
  rcases (show (0 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 120) ∨ (120 ≤ k ∧ k < 150) ∨ (150 ≤ k ∧ k < 180) ∨ (180 ≤ k ∧ k < 210) ∨ (210 ≤ k ∧ k < 240) ∨ (240 ≤ k ∧ k < 270) ∨ (270 ≤ k ∧ k < 300) ∨ (300 ≤ k ∧ k < 330) ∨ (330 ≤ k ∧ k < 357) by omega) with ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩
  · exact RtPremC.StepsM.ctlSegM_00 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtPremC.StepsM.ctlSegM_01 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtPremC.StepsM.ctlSegM_02 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtPremC.StepsM.ctlSegM_03 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtPremC.StepsM.ctlSegM_04 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtPremC.StepsM.ctlSegM_05 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtPremC.StepsM.ctlSegM_06 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtPremC.StepsM.ctlSegM_07 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtPremC.StepsM.ctlSegM_08 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtPremC.StepsM.ctlSegM_09 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtPremC.StepsM.ctlSegM_10 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtPremC.StepsM.ctlSegM_11 real spec config rows mapping base pins entry budget dp hb k lo hi


/-- Translation-control vector and descriptor-footprint bytes constant along the heap-v2 normal path. -/
theorem ctl_body (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, k ≤ 357 → CtlRel spec entry (stateAt real entry k) := by
  have h := (e17_general real spec config rows mapping base pins entry budget dp hb).1
  intro k hk
  induction k with
  | zero => exact CtlRel.refl spec entry
  | succ k ih =>
    obtain ⟨fin, run, rel⟩ := ctlStepsM real spec config rows mapping base pins entry budget dp hb k (by omega)
      (stateAt real entry k) (h k (by omega)).1
    rw [RtDit.stateAt_succ_of run]
    exact (ih (by omega)).trans rel

/-- The body's final RET (k = 357, to X30) keeps them too: state 358 (the shim's σ 365). -/
theorem ctl_body_ret (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 358 ≤ budget)
    (hlow : ((stateAt real entry 357).regs.gpr[(GPRSummary.key (30#5).toNat).val]).toNat < 2 ^ 55) :
    CtlRel spec entry (stateAt real entry 358) := by
  have h := (e17_general real spec config rows mapping base pins entry budget dp (by omega)).1
  have inv := (h 357 (by omega)).1
  have b := ctl_body real spec config rows mapping base pins entry budget dp (by omega) 357 (by omega)
  obtain ⟨fin, run, rel⟩ := RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget
    pins 357 (by omega) dp.page (by decide +kernel) _ _ inv.v3
    (MemNext.memFetch spec config rows mapping base budget 357 pins (rowsFootprint spec.imageRows).byte dp.static 0xc0 0xd65f03c0
      (by decide +kernel) (by decide +kernel) _ (by decide) _ inv.v3.v2)
    (fun _ => True) (RtPremC.ctl_retM real 30#5 (by decide) (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True) hlow)
  rw [RtDit.stateAt_succ_of run]
  exact b.trans rel

#print axioms ctlStepsM
#print axioms ctl_body
#print axioms ctl_body_ret
end RtPremC
