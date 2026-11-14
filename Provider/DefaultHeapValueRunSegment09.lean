-- Current-profile heap body with exact ordered records.
import DefaultHeapBody
import ArmCertValue.Glue
import ArmCertValue.HP1Run
import ArmCertValueMem.Classes
import DefaultHeapValueClassRows04
import DefaultHeapValueClassRows05
import DefaultHeapValueClassRows06
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxGenGuarded HeapV2StepCerts
open CertiFFI.Prog.Generic.ModelRunView
open HeapV2StepCerts.E17General (qOf low_of)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
namespace ReleaseProfile.DefaultHeapRun


#check "CURRENT_DECL heap value_segment_09"
theorem value_segment_09 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) (dbl : ArmCertValue.HeapV2Mem.DataBytesLinear pins mapping)
    (inj : ArmCertValue.HeapV2Mem.RegionsInjective pins mapping) :
    ∀ k, 270 ≤ k → k < 300 → ∀ h : k < ArmCertValue.HeapV2Plan.plan.length,
      ArmCertValue.StepFact real ((fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore))
      mapping (HeapV2E17.pin pins) ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan k h := by
  intro k lo hi h
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_270 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_271 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_272 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_273 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_274 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_275 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_276 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_277 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_278 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_279 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_280 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_281 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_282 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_283 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_284 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_285 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_286 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_287 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_288 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_289 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_290 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_291 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_292 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_293 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_294 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_295 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_296 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_297 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_298 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_299 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  omega
#print axioms value_segment_09
end ReleaseProfile.DefaultHeapRun
