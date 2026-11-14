-- Current-profile heap body with exact ordered records.
import DefaultHeapBody
import ArmCertValue.Glue
import ArmCertValue.HP1Run
import ArmCertValueMem.Classes
import DefaultHeapValueBranchRows
import DefaultHeapValueClassRows01
import DefaultHeapValueClassRows02
import DefaultHeapValueMemStepRows02
import DefaultHeapValueMemStepRows03
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxGenGuarded HeapV2StepCerts
open CertiFFI.Prog.Generic.ModelRunView
open HeapV2StepCerts.E17General (qOf low_of)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
namespace ReleaseProfile.DefaultHeapRun


#check "CURRENT_DECL heap value_segment_04"
theorem value_segment_04 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) (dbl : ArmCertValue.HeapV2Mem.DataBytesLinear pins mapping)
    (inj : ArmCertValue.HeapV2Mem.RegionsInjective pins mapping) :
    ∀ k, 120 ≤ k → k < 150 → ∀ h : k < ArmCertValue.HeapV2Plan.plan.length,
      ArmCertValue.StepFact real ((fun k => RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore))
      mapping (HeapV2E17.pin pins) ArmCertValue.HeapV2Plan.regions ArmCertValue.HeapV2Plan.plan k h := by
  intro k lo hi h
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_120 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapRun.value_branch_121 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_122 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_123 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_124 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapRun.value_branch_125 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_126 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_127 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_128 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapRun.value_branch_129 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_130 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_131 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_132 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapRun.value_branch_133 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_134 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_135 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_136 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapRun.value_branch_137 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_138 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_139 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_140 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapRun.value_branch_141 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_142 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueMem.stepV_143 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb dbl inj
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_144 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapRun.value_branch_145 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapRun.value_branch_146 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_147 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_148 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · exact ReleaseProfile.DefaultHeapValueSteps.stepV_149 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
  omega
#print axioms value_segment_04
end ReleaseProfile.DefaultHeapRun
