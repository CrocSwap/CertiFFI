import DitShim243.Initial
import DitShim243.Factory
import DitShim243.GeometryFacts
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open TranslateSpan TranslateSpan.SecpRawDeployment HeapV2StepCerts NativeMteTagCheck ReleaseProfile ArmCertValue ArmCertPipe
open CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace DitShim243.Prologue

theorem of_initial (real : Type) [Sail.SailReal real]
    (p : Plan) (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (image : MemReloc.Image)
    (start : Nat) (imm : BitVec 26) (L : Nat) (pins : HeapV2E17.Pins) (capacity : Nat) (entry : NativeState) (catalogue : ControlCatalogue)
    (gt : CheckedTopology.check raw (Deployment.addresses p base entry start imm (BitVec.ofNat 64 pins.sp)) 4 = true)
    (rt : CheckedTopology.check raw (SecpRawDeployment.addresses p base entry) 4 = true)
    (info : Initial.Info p raw config rows mapping base image start imm L pins capacity entry catalogue gt rt) :
    Pre.ShimPreMG real L (CheckedTopology.spec raw (Deployment.addresses p base entry start imm (BitVec.ofNat 64 pins.sp)) 4 gt)
      config rows mapping pins (Deployment.consumer p raw mapping base entry start imm (BitVec.ofNat 64 pins.sp))
      start (· ∈ codeOffsets (Deployment.extend p start imm)) image base base (InitialCheck.runOffset p start L base entry)
      (L+12) catalogue capacity entry ∧
      (stateAt real entry 3).regs.gpr[9].extractLsb 24 24 = entry.regs.PSTATE.DIT := by
  exact Factory.prologue real L _ config rows mapping pins _ start imm _ image base _ (L+12) _ capacity entry
    (Nat.le_refl _) info.metadata.page
    (Geometry.whole_aligned start (InitialCheck.rawPC p) L base (entryGPR entry 30)
      info.metadata.startAligned info.metadata.bodyAligned)
    (fun j hj => Geometry.whole_prefix start (InitialCheck.rawPC p) L j base (entryGPR entry 30) hj)
    (fun j lo hi => Geometry.whole_epilogue start (InitialCheck.rawPC p) L j base (entryGPR entry 30) lo hi)
    info.metadata.nodup info.codeSlot info.current info.status info.code
    (by have := info.metadata.rowRoom; omega) info.metadata.mrs info.metadata.isb info.metadata.residue
    info.slotPresent info.metadata.sp
    (Deployment.slot_permitted p raw mapping base entry start imm pins info.metadata.slotAligned)
    info.slots info.metadata.slotAligned info.metadata.land info.metadata.bodyLow

#print axioms of_initial
end DitShim243.Prologue
