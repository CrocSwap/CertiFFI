import PipeLean_D234_SecpMul_c17.DitBodyState
import DitShim243.BodyEntry
import DitShim243.Prologue
import TranslateSpan.DefaultFiniteRows
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmCert.Translate.Model.StaticPie
open TranslateSpan TranslateSpan.SecpRawDeployment HeapV2StepCerts NativeMteTagCheck ReleaseProfile ArmCertValue ArmCertPipe
open CertiFFI.Prog.Generic.ModelRunView DitShim243
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpMul_c17.DitBodyEntry

section Entry
variable (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (start : Nat) (imm : BitVec 26) (pins : HeapV2E17.Pins) (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (gt : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry start imm (BitVec.ofNat 64 pins.sp)) 4 = true)
    (rt : CheckedTopology.check raw (SecpRawDeployment.addresses EntryBinding.plan base entry) 4 = true)
    (info : Initial.Info EntryBinding.plan raw config rows mapping base (referenceImageI SecpArtifact.elf base (fun _ => 0))
      start imm 157 pins (DefaultState.capacity entry + 2) entry catalogue gt rt)
    (pre : Pre.ShimPreMG real 157 (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry start imm (BitVec.ofNat 64 pins.sp)) 4 gt)
      config rows mapping pins (Deployment.consumer EntryBinding.plan raw mapping base entry start imm (BitVec.ofNat 64 pins.sp))
      start (· ∈ codeOffsets (Deployment.extend EntryBinding.plan start imm)) (referenceImageI SecpArtifact.elf base (fun _ => 0)) base base
      (InitialCheck.runOffset EntryBinding.plan start 157 base entry) 169 catalogue (DefaultState.capacity entry+2) entry)
include info pre

theorem of_pre :
    ∃ rt7 : CheckedTopology.check raw (SecpRawDeployment.addresses EntryBinding.plan base (stateAt real entry 7)) 4 = true,
      DitBodyState.Receipt raw config rows mapping base (stateAt real entry 7) catalogue rt7 := by
  have pinsChecked : DataFrame.checkPins EntryBinding.plan = true := by decide
  have agree := DataTransport.of_pre real 157 _ config rows mapping pins _ start _ _ base base _ 169 _ (DefaultState.capacity entry+2) entry pre EntryBinding.plan pinsChecked
  obtain ⟨rt7,core⟩ := BodyEntry.core real EntryBinding.plan raw config rows mapping base _ start imm 157 pins (DefaultState.capacity entry+2) entry catalogue gt rt info pre pinsChecked
  have present := DataTransport.present agree
  have initialAgreement : ValuePlan.AgreesAt .g (view EntryBinding.plan mapping (stateAt real entry 7))
      regions_c00 σ0_c00 (Default.inputs mapping (stateAt real entry 7))
      (plan_c00 ((stateAt real entry 7).regs.bank_BitVec_64 .TPIDR_EL0)) 0 (stateAt real entry 7) := by
    exact ValuePlan.initial .g _ _ _ _ _ _
      (Physical.Entry.snapshot_agrees _ _ EntryBinding.plan.regions (fun g j i k member => present g j i k member (info.present g j i k member)))
      (Physical.Entry.snapshot_bounded _ _ EntryBinding.plan.regions)
  have capacityEq : DefaultState.capacity (stateAt real entry 7) = DefaultState.capacity entry :=
    DataTransport.budget agree _
  obtain ⟨draws,delta,bound⟩ := pre.choice7
  have status : TagStatusRows (stateAt real entry 7) ((stateAt real entry 7).choiceOcc.getD 1354 0)
      (DefaultState.capacity (stateAt real entry 7)) := by
    exact DefaultMTE2.rows_after_delta entry (stateAt real entry 7) (DefaultState.capacity entry+2)
      (DefaultState.capacity (stateAt real entry 7)) draws info.status delta (by omega)
  refine ⟨rt7,⟨⟨core,pre.inv7.branch,initialAgreement,status,0,choice_delta_refl _,?_⟩,
    DataTransport.layout agree raw base info.rawLayout,info.metadata.page,?_,?_,DataTransport.spans agree info.spans⟩⟩
  · exact Nat.zero_le _
  · rw [entryGPR,dif_pos (show 30 < 31 by decide),pre.x30_7]
    have off : InitialCheck.runOffset EntryBinding.plan start 157 base entry 165 = Geometry.shimPC start 7 :=
      Geometry.whole_epilogue start (InitialCheck.rawPC EntryBinding.plan) 157 165 base (entryGPR entry 30) (by decide) (by decide)
    rw [off]
    exact info.metadata.continuationLow
  · rw [DataTransport.sites agree]
    exact info.targets

end Entry
#print axioms of_pre
end PipeLean_D234_SecpMul_c17.DitBodyEntry
