-- Current-profile heap body with exact ordered records.
import DefaultHeapBody
import ArmCertValue.Glue
import ArmCertValue.HP1Run
import ArmCertValueMem.Classes
import DefaultHeapValueBranchRows
import DefaultHeapValueClassRows00
import DefaultHeapValueClassRows01
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


#check "CURRENT_DECL heap value_segment_02"
theorem value_segment_02 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) (dbl : ArmCertValue.HeapV2Mem.DataBytesLinear pins mapping)
    (inj : ArmCertValue.HeapV2Mem.RegionsInjective pins mapping) :
    ∀ k, 60 ≤ k → k < 90 → ∀ h : k < ArmCertValue.HeapV2Plan.plan.length,
      ArmCertValue.StepFact real ((fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore))
      mapping (HeapV2E17.pin pins) ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan k h := by
  intro k lo hi h
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_60 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapRun.value_branch_61 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_62 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_63 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_64 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapRun.value_branch_65 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_66 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_67 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_68 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapRun.value_branch_69 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_70 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_71 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_72 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapRun.value_branch_73 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_74 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_75 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_76 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapRun.value_branch_77 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_78 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_79 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_80 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapRun.value_branch_81 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_82 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_83 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_84 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapRun.value_branch_85 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_86 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_87 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_88 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapRun.value_branch_89 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  omega
#print axioms value_segment_02
end ReleaseProfile.DefaultHeapRun
