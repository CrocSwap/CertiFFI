-- (H-P4 + D180a (1), /): the heap-v2 body keeps PSTATE.DIT on the whole
-- normal path over any e17_general deployment: ditSteps (every step k < 357 keeps DIT, from its actual tail)
-- and dit_body (∀ k ≤ 357, DIT (stateAt entry k) = DIT entry), composed along e17_general's I4 chain.
import RtDit.DitSeg_00
import RtDit.DitSeg_01
import RtDit.DitSeg_02
import RtDit.DitSeg_03
import RtDit.DitSeg_04
import RtDit.DitSeg_05
import RtDit.DitSeg_06
import RtDit.DitSeg_07
import RtDit.DitSeg_08
import RtDit.DitSeg_09
import RtDit.DitSeg_10
import RtDit.DitSeg_11
import HeapV2StepCerts.E17General.Assembly
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV4 HeapV2StepCerts.E17General
open ArmBridge.Boundary ArmBridge.CruxCore
open CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false
namespace RtDit

theorem ditSteps (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, k < 357 → DitStep real spec config rows mapping base pins entry budget k := by
  intro k hk
  rcases (show (0 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 120) ∨ (120 ≤ k ∧ k < 150) ∨ (150 ≤ k ∧ k < 180) ∨ (180 ≤ k ∧ k < 210) ∨ (210 ≤ k ∧ k < 240) ∨ (240 ≤ k ∧ k < 270) ∨ (270 ≤ k ∧ k < 300) ∨ (300 ≤ k ∧ k < 330) ∨ (330 ≤ k ∧ k < 357) by omega) with ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩
  · exact RtDit.Steps.ditSeg_00 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtDit.Steps.ditSeg_01 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtDit.Steps.ditSeg_02 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtDit.Steps.ditSeg_03 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtDit.Steps.ditSeg_04 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtDit.Steps.ditSeg_05 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtDit.Steps.ditSeg_06 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtDit.Steps.ditSeg_07 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtDit.Steps.ditSeg_08 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtDit.Steps.ditSeg_09 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtDit.Steps.ditSeg_10 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact RtDit.Steps.ditSeg_11 real spec config rows mapping base pins entry budget dp hb k lo hi

theorem stateAt_succ_of {real : Type} [Sail.SailReal real] {s fin : NativeState} {k : Nat}
    (run : modelStep real (stateAt real s k) = .ok () fin) : stateAt real s (k + 1) = fin := by
  show next real (stateAt real s k) = fin
  unfold next; rw [run]

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.dit_body"
  (← IO.getStderr).flush

/-- D180a body frame: PSTATE.DIT is constant along the heap-v2 normal path. -/
theorem dit_body (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, k ≤ 357 → (stateAt real entry k).regs.PSTATE.DIT = entry.regs.PSTATE.DIT := by
  have h := (e17_general real spec config rows mapping base pins entry budget dp hb).1
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨fin, run, dit⟩ := ditSteps real spec config rows mapping base pins entry budget dp hb k (by omega)
      (stateAt real entry k) (h k (by omega)).1
    rw [stateAt_succ_of run, dit, ih (by omega)]

#print axioms ditSteps
#print axioms dit_body
end RtDit
