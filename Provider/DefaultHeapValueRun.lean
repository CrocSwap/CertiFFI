-- Current-profile heap body with exact ordered records.
import DefaultHeapValueRunSegment00
import DefaultHeapValueRunSegment01
import DefaultHeapValueRunSegment02
import DefaultHeapValueRunSegment03
import DefaultHeapValueRunSegment04
import DefaultHeapValueRunSegment05
import DefaultHeapValueRunSegment06
import DefaultHeapValueRunSegment07
import DefaultHeapValueRunSegment08
import DefaultHeapValueRunSegment09
import DefaultHeapValueRunSegment10
import DefaultHeapValueRunSegment11
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxGenGuarded HeapV2StepCerts
open CertiFFI.Prog.Generic.ModelRunView
open HeapV2StepCerts.E17General (qOf low_of)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
namespace ReleaseProfile.DefaultHeapRun


theorem value_steps (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) (dbl : ArmCertValue.HeapV2Mem.DataBytesLinear pins mapping)
    (inj : ArmCertValue.HeapV2Mem.RegionsInjective pins mapping) :
    ∀ k (h : k < ArmCertValue.HeapV2Plan.plan.length), ArmCertValue.StepFact real ((fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore))
      mapping (HeapV2E17.pin pins) ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan k h := by
  intro k h
  have hk : k < 357 := by simpa only [ArmCertValue.HeapV2Plan.plan_length] using h
  rcases (show (0 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 120) ∨ (120 ≤ k ∧ k < 150) ∨ (150 ≤ k ∧ k < 180) ∨ (180 ≤ k ∧ k < 210) ∨ (210 ≤ k ∧ k < 240) ∨ (240 ≤ k ∧ k < 270) ∨ (270 ≤ k ∧ k < 300) ∨ (300 ≤ k ∧ k < 330) ∨ (330 ≤ k ∧ k < 357) by omega) with ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩
  · exact value_segment_00 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj k lo hi h
  · exact value_segment_01 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj k lo hi h
  · exact value_segment_02 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj k lo hi h
  · exact value_segment_03 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj k lo hi h
  · exact value_segment_04 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj k lo hi h
  · exact value_segment_05 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj k lo hi h
  · exact value_segment_06 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj k lo hi h
  · exact value_segment_07 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj k lo hi h
  · exact value_segment_08 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj k lo hi h
  · exact value_segment_09 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj k lo hi h
  · exact value_segment_10 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj k lo hi h
  · exact value_segment_11 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj k lo hi h
#print axioms value_steps
end ReleaseProfile.DefaultHeapRun
