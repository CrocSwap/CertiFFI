-- Current-profile heap body with exact ordered records.
import DefaultHeapRunSegment00
import DefaultHeapRunSegment01
import DefaultHeapRunSegment02
import DefaultHeapRunSegment03
import DefaultHeapRunSegment04
import DefaultHeapRunSegment05
import DefaultHeapRunSegment06
import DefaultHeapRunSegment07
import DefaultHeapRunSegment08
import DefaultHeapRunSegment09
import DefaultHeapRunSegment10
import DefaultHeapRunSegment11
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxGenGuarded HeapV2StepCerts
open CertiFFI.Prog.Generic.ModelRunView
open HeapV2StepCerts.E17General (qOf low_of)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
namespace ReleaseProfile.DefaultHeapRun

#check "CURRENT_DECL default heap steps"
theorem steps (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ∀ k, k < 357 → DefaultHeapResidue.Step real spec mapping (records spec pins k)
      (RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) (RunInv spec config rows mapping base pins entry budget (k + 1) catalogue capacity drawsBefore) := by
  intro k hk
  rcases (show (0 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 120) ∨ (120 ≤ k ∧ k < 150) ∨ (150 ≤ k ∧ k < 180) ∨ (180 ≤ k ∧ k < 210) ∨ (210 ≤ k ∧ k < 240) ∨ (240 ≤ k ∧ k < 270) ∨ (270 ≤ k ∧ k < 300) ∨ (300 ≤ k ∧ k < 330) ∨ (330 ≤ k ∧ k < 357) by omega) with ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩
  · exact segment_00 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo hi
  · exact segment_01 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo hi
  · exact segment_02 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo hi
  · exact segment_03 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo hi
  · exact segment_04 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo hi
  · exact segment_05 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo hi
  · exact segment_06 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo hi
  · exact segment_07 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo hi
  · exact segment_08 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo hi
  · exact segment_09 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo hi
  · exact segment_10 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo hi
  · exact segment_11 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo hi

#check "CURRENT_DECL default heap prefixes"
theorem prefixes (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ∀ k, k ≤ 357 → RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore (stateAt real entry k) := by
  apply invariant_prefixes real (fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore) 357 _ entry (initial dp)
  intro k hk x invariant
  obtain ⟨fin, run, next, _, _⟩ := steps real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k hk x invariant
  exact ⟨fin, run, next⟩

#print axioms steps
#print axioms prefixes
end ReleaseProfile.DefaultHeapRun
