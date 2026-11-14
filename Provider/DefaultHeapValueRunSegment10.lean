-- Current-profile heap body with exact ordered records.
import DefaultHeapBody
import ArmCertValue.Glue
import ArmCertValue.HP1Run
import ArmCertValueMem.Classes
import DefaultHeapValueClassRows06
import DefaultHeapValueClassRows07
import DefaultHeapValueMemStepRows04
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxGenGuarded HeapV2StepCerts
open CertiFFI.Prog.Generic.ModelRunView
open HeapV2StepCerts.E17General (qOf low_of)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
namespace ReleaseProfile.DefaultHeapRun


#check "CURRENT_DECL heap value_segment_10"
theorem value_segment_10 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) (dbl : ArmCertValue.HeapV2Mem.DataBytesLinear pins mapping)
    (inj : ArmCertValue.HeapV2Mem.RegionsInjective pins mapping) :
    ∀ k, 300 ≤ k → k < 330 → ∀ h : k < ArmCertValue.HeapV2Plan.plan.length,
      ArmCertValue.StepFact real ((fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore))
      mapping (HeapV2E17.pin pins) ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan k h := by
  intro k lo hi h
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_300 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_301 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_302 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_303 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_304 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_305 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_306 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_307 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_308 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_309 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_310 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_311 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_312 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_313 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_314 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_315 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_316 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_317 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_318 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_319 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_320 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_321 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_322 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_323 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_324 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_325 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_326 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_327 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_328 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_329 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  omega
#print axioms value_segment_10
end ReleaseProfile.DefaultHeapRun
