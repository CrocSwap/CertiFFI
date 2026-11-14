import DitShim243.DataTransport
import DitShim243.CurrentBridge
import DitShim243.Factory
import DitShim243.GeometryFacts
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open TranslateSpan TranslateSpan.SecpRawDeployment HeapV2StepCerts NativeMteTagCheck ReleaseProfile ArmCertValue ArmCertPipe
open CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace DitShim243.BodyEntry

theorem core (real : Type) [Sail.SailReal real]
    (p : Plan) (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (image : MemReloc.Image)
    (start : Nat) (imm : BitVec 26) (L : Nat) (pins : HeapV2E17.Pins) (capacity : Nat) (entry : NativeState) (catalogue : ControlCatalogue)
    (gt : CheckedTopology.check raw (Deployment.addresses p base entry start imm (BitVec.ofNat 64 pins.sp)) 4 = true)
    (rt : CheckedTopology.check raw (SecpRawDeployment.addresses p base entry) 4 = true)
    (info : Initial.Info p raw config rows mapping base image start imm L pins capacity entry catalogue gt rt)
    (pre : Pre.ShimPreMG real L (CheckedTopology.spec raw (Deployment.addresses p base entry start imm (BitVec.ofNat 64 pins.sp)) 4 gt)
      config rows mapping pins (Deployment.consumer p raw mapping base entry start imm (BitVec.ofNat 64 pins.sp))
      start (· ∈ codeOffsets (Deployment.extend p start imm)) image base base (InitialCheck.runOffset p start L base entry)
      (L+12) catalogue capacity entry)
    (pinsChecked : DataFrame.checkPins p = true) :
    ∃ rt7 : CheckedTopology.check raw (SecpRawDeployment.addresses p base (stateAt real entry 7)) 4 = true,
    DefaultMTE2.Core (CheckedTopology.spec raw (SecpRawDeployment.addresses p base (stateAt real entry 7)) 4 rt7)
      config rows mapping (SecpRawDeployment.consumer p raw mapping base (stateAt real entry 7))
      (· ∈ codeOffsets p) image base base (offset p) (p.code.length+4)
      (profile (stateAt real entry 7)) catalogue 0 (stateAt real entry 7) := by
  have agree := DataTransport.of_pre real L _ config rows mapping pins _ start _ image base base _ (L+12) _ capacity entry pre p pinsChecked
  have rt7 : CheckedTopology.check raw (SecpRawDeployment.addresses p base (stateAt real entry 7)) 4 = true := by
    rw [DataTransport.addresses agree base]; exact rt
  refine ⟨rt7,?_⟩
  have pf : NativeAccess.ProfileAt (profile (stateAt real entry 7)) (stateAt real entry 7) := by
    apply DataFrame.profile_current pre.inv7.controls pre.inv7.feat.2.2.2
    rw [← info.current.controls.preparation.2.1]
    exact info.profileAt.alignment_disabled
  have result := CurrentBridge.to_raw raw _ _ 4 gt rt7 config rows mapping
    (Deployment.consumer p raw mapping base entry start imm (BitVec.ofNat 64 pins.sp))
    (SecpRawDeployment.consumer p raw mapping base (stateAt real entry 7))
    (· ∈ codeOffsets (Deployment.extend p start imm)) (· ∈ codeOffsets p) image base base
    (InitialCheck.runOffset p start L base entry) (offset p) (L+12) (p.code.length+4) 7 0
    catalogue (profile (stateAt real entry 7)) (stateAt real entry 7) pre.inv7
    (by simpa only [InitialCheck.runOffset,offset,InitialCheck.rawPC,Nat.mul_zero,Nat.add_zero] using
      Geometry.whole_body start (InitialCheck.rawPC p) L base (entryGPR entry 30) 0 (Nat.zero_le L))
    (by have := info.metadata.length; omega)
    (fun o ho => by simpa only [SecpRawDeployment.codeOffsets,Deployment.extend,List.flatMap_append,List.mem_append] using Or.inl ho)
    (fun va acc aligned size permitted => by
      rw [DataTransport.consumer agree raw base] at permitted
      exact Deployment.raw_subset p raw mapping base entry start imm (BitVec.ofNat 64 pins.sp) va acc aligned size permitted)
    (DataTransport.domain_initial agree raw config rows base rt info.rawClosed) pf
  exact result

#print axioms core
end DitShim243.BodyEntry
