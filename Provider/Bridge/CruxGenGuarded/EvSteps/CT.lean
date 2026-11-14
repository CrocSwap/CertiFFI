import Bridge.CruxGenGuarded.EvSteps.EvSeg_00
import Bridge.CruxGenGuarded.EvSteps.EvSeg_01
import Bridge.CruxGenGuarded.EvSteps.EvSeg_02
import Bridge.CruxGenGuarded.EvSteps.EvSeg_03
import Bridge.CruxGenGuarded.EvSteps.EvSeg_04
import Bridge.CruxGenGuarded.EvSteps.EvSeg_05
import Bridge.CruxGenGuarded.EvSteps.EvSeg_06
import Bridge.CruxGenGuarded.EvSteps.EvSeg_07
import Bridge.CruxGenGuarded.EvSteps.EvSeg_08
import Bridge.CruxGenGuarded.EvSteps.EvSeg_09
import Bridge.CruxGenGuarded.EvSteps.EvSeg_10
import Bridge.CruxGenGuarded.EvSteps.EvSeg_11
import HeapV2StepCerts.E17General.Assembly
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
namespace ArmBridge.CruxGenGuarded.EvSteps
open ArmBridge.Draft ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV4 HeapV2StepCerts.E17General
open ArmBridge.Boundary ArmBridge.CruxCore
open CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! GENERATED (gen_ev_steps companion). two-run CT0 for the heap-v2 normal path over any
deployment satisfying e17_general's DeploymentPremises: two entries with the same spec, mapping,
base and pins (everything else, including all data memory and unbound registers, may differ)
produce record-equal ordered event traces (frozen OrderedEventV2.record) over the whole
357-step run, and land on equal PCs. Each step's appended events have a single-run shape
(EvShape: fetch traffic of the PC, then the step's plan data access) that depends only on
public data; PhasedCT.phased_records composes them. -/

theorem evSteps (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, k < 357 → EvStep real spec config rows mapping base pins entry budget k := by
  intro k hk
  rcases (show (0 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 120) ∨ (120 ≤ k ∧ k < 150) ∨ (150 ≤ k ∧ k < 180) ∨ (180 ≤ k ∧ k < 210) ∨ (210 ≤ k ∧ k < 240) ∨ (240 ≤ k ∧ k < 270) ∨ (270 ≤ k ∧ k < 300) ∨ (300 ≤ k ∧ k < 330) ∨ (330 ≤ k ∧ k < 357) by omega) with ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩
  · exact evSeg_00 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact evSeg_01 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact evSeg_02 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact evSeg_03 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact evSeg_04 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact evSeg_05 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact evSeg_06 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact evSeg_07 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact evSeg_08 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact evSeg_09 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact evSeg_10 real spec config rows mapping base pins entry budget dp hb k lo hi
  · exact evSeg_11 real spec config rows mapping base pins entry budget dp hb k lo hi

theorem stateAt_succ_of {real : Type} [Sail.SailReal real] {s fin : NativeState} {k : Nat}
    (run : modelStep real (stateAt real s k) = .ok () fin) : stateAt real s (k + 1) = fin := by
  show next real (stateAt real s k) = fin
  unfold next; rw [run]

run_cmd do
  IO.eprintln "CURRENT_DECL EvSteps.ct_general"
  (← IO.getStderr).flush

/-- CT0, heap-v2 normal path, general deployment. -/
theorem ct_general (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (el er : NativeState) (budget : Nat)
    (dpl : DeploymentPremises spec config rows mapping base pins el budget)
    (dpr : DeploymentPremises spec config rows mapping base pins er budget) (hb : 357 ≤ budget) :
    PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record el er (stateAt real el 357) (stateAt real er 357) := by
  have hl := (e17_general real spec config rows mapping base pins el budget dpl hb).1
  have hr := (e17_general real spec config rows mapping base pins er budget dpr hb).1
  have pcEq : ∀ j, j ≤ 357 → (stateAt real el j).regs._PC = (stateAt real er j).regs._PC := fun j hj =>
    (hl j hj).1.v3.v2.v1.pc.trans (hr j hj).1.v3.v2.v1.pc.symm
  have main := PhasedCT.phased_records (fun k => stateAt real el k) (fun k => stateAt real er k)
    (fun _ _ _ => True) 357 trivial (pcEq 0 (by omega)) (by
      intro k hk _
      obtain ⟨fl, runl, evl⟩ := evSteps real spec config rows mapping base pins el budget dpl hb k hk
        (stateAt real el k) (hl k (by omega)).1
      obtain ⟨fr, runr, evr⟩ := evSteps real spec config rows mapping base pins er budget dpr hb k hk
        (stateAt real er k) (hr k (by omega)).1
      have sl := stateAt_succ_of runl
      have sr := stateAt_succ_of runr
      refine ⟨?_, trivial⟩
      show PhasedCT.TimingRec _ (stateAt real el k) (stateAt real er k) (stateAt real el (k + 1)) (stateAt real er (k + 1))
      have pf := pcEq (k + 1) (by omega)
      rw [sl, sr] at pf ⊢
      exact StepEvents.pair spec mapping (dataOf spec pins k) _ _ fl fr evl evr (pcEq k (by omega)) pf)
  exact main

#print axioms evSteps
#print axioms ct_general
end ArmBridge.CruxGenGuarded.EvSteps
