-- Current-profile heap body with exact ordered records.
import DefaultHeapBody
import ArmCertValue.Glue
import ArmCertValue.HP1Run
import ArmCertValueMem.Classes
import DefaultHeapValueBranchRows
import DefaultHeapValueClassRows00
import DefaultHeapValueMemStepRows00
import DefaultHeapValueMemStepRows01
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxGenGuarded HeapV2StepCerts
open CertiFFI.Prog.Generic.ModelRunView
open HeapV2StepCerts.E17General (qOf low_of)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
namespace ReleaseProfile.DefaultHeapRun


#check "CURRENT_DECL heap value_segment_01"
theorem value_segment_01 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) (dbl : ArmCertValue.HeapV2Mem.DataBytesLinear pins mapping)
    (inj : ArmCertValue.HeapV2Mem.RegionsInjective pins mapping) :
    ∀ k, 30 ≤ k → k < 60 → ∀ h : k < ArmCertValue.HeapV2Plan.plan.length,
      ArmCertValue.StepFact real ((fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore))
      mapping (HeapV2E17.pin pins) ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan k h := by
  intro k lo hi h
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_30 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_31 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_32 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapRun.value_branch_33 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_34 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_35 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_36 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapRun.value_branch_37 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_38 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_39 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_40 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapRun.value_branch_41 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_42 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_43 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_44 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapRun.value_branch_45 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_46 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_47 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_48 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapRun.value_branch_49 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_50 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_51 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_52 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapRun.value_branch_53 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_54 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_55 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_56 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapRun.value_branch_57 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_58 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_59 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  omega
#print axioms value_segment_01
end ReleaseProfile.DefaultHeapRun
