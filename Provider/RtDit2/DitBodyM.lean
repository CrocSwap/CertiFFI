-- (H-P4 (2) groundwork): the heap-v2 body keeps PSTATE.DIT AND writes only the plan's data bytes
-- (MemFrame (dataBytes pins mapping)) on the whole run, including the final RET at k = 357 (to X30):
-- dit_body_mem (∀ k ≤ 357) and dit_body_ret (state 358, the RET's landing, e.g. the shim's s7).
import RtDit2.DitSegM_00
import RtDit2.DitSegM_01
import RtDit2.DitSegM_02
import RtDit2.DitSegM_03
import RtDit2.DitSegM_04
import RtDit2.DitSegM_05
import RtDit2.DitSegM_06
import RtDit2.DitSegM_07
import RtDit2.DitSegM_08
import RtDit2.DitSegM_09
import RtDit2.DitSegM_10
import RtDit2.DitSegM_11
import RtDit.DitBody
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV4 HeapV2StepCerts.E17General
open ArmBridge.Boundary ArmBridge.CruxCore HeapV2StepCerts
open CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false
namespace RtDit

theorem ditStepsM (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, k < 357 → DitStepM real spec config rows mapping base pins entry budget k := by
  intro k hk
  rcases (show (0 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 120) ∨ (120 ≤ k ∧ k < 150) ∨ (150 ≤ k ∧ k < 180) ∨ (180 ≤ k ∧ k < 210) ∨ (210 ≤ k ∧ k < 240) ∨ (240 ≤ k ∧ k < 270) ∨ (270 ≤ k ∧ k < 300) ∨ (300 ≤ k ∧ k < 330) ∨ (330 ≤ k ∧ k < 357) by omega) with ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩
  · exact RtDit.StepsM.ditSegM_00 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtDit.StepsM.ditSegM_01 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtDit.StepsM.ditSegM_02 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtDit.StepsM.ditSegM_03 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtDit.StepsM.ditSegM_04 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtDit.StepsM.ditSegM_05 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtDit.StepsM.ditSegM_06 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtDit.StepsM.ditSegM_07 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtDit.StepsM.ditSegM_08 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtDit.StepsM.ditSegM_09 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtDit.StepsM.ditSegM_10 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtDit.StepsM.ditSegM_11 real spec config rows mapping base pins entry budget dp hb k lo hi

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.dit_body_mem"
  (← IO.getStderr).flush

/-- DIT constant and only the plan's data bytes written, along the heap-v2 normal path. -/
theorem dit_body_mem (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, k ≤ 357 → (stateAt real entry k).regs.PSTATE.DIT = entry.regs.PSTATE.DIT ∧
      MemFrame (MemNext.dataBytes pins mapping) entry (stateAt real entry k) := by
  have h := (e17_general real spec config rows mapping base pins entry budget dp hb).1
  intro k hk
  induction k with
  | zero => exact ⟨rfl, fun _ _ => rfl⟩
  | succ k ih =>
    obtain ⟨fin, run, dit, fr⟩ := ditStepsM real spec config rows mapping base pins entry budget dp hb k (by omega)
      (stateAt real entry k) (h k (by omega)).1
    rw [stateAt_succ_of run]
    exact ⟨dit.trans (ih (by omega)).1, (ih (by omega)).2.trans fr⟩

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.dit_body_ret"
  (← IO.getStderr).flush

/-- The body's final RET (k = 357, to X30) also keeps DIT and writes nothing. -/
theorem dit_body_ret (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 358 ≤ budget)
    (hlow : ((stateAt real entry 357).regs.gpr[(GPRSummary.key (30#5).toNat).val]).toNat < 2 ^ 55) :
    (stateAt real entry 358).regs.PSTATE.DIT = entry.regs.PSTATE.DIT ∧
      MemFrame (MemNext.dataBytes pins mapping) entry (stateAt real entry 358) := by
  have h := (e17_general real spec config rows mapping base pins entry budget dp (by omega)).1
  have inv := (h 357 (by omega)).1
  obtain ⟨b1, b2⟩ := dit_body_mem real spec config rows mapping base pins entry budget dp (by omega) 357 (by omega)
  obtain ⟨fin, run, dit, fr⟩ := RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget
    pins 357 (by omega) dp.page (by decide +kernel) _ _ inv.v3
    (MemNext.memFetch spec config rows mapping base budget 357 pins (rowsFootprint spec.imageRows).byte dp.static 0xc0 0xd65f03c0
      (by decide +kernel) (by decide +kernel) _ (by decide) _ inv.v3.v2)
    _ (RtDit.dit_retM real 30#5 (by decide) (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch _ hlow)
  rw [stateAt_succ_of run]
  exact ⟨dit.trans b1, b2.trans fr⟩

#print axioms ditStepsM
#print axioms dit_body_mem
#print axioms dit_body_ret
end RtDit
