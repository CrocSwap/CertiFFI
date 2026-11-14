import PipeLean_D234_SecpMulAlt_c19.DitBodyEntry
import PipeLean_D234_SecpMulAlt_c19.DitBodyABI
import PipeLean_D234_SecpMulAlt_c19.DitBodyFrames
import DitShim243.ClosedTransport
import DitShim243.BodyFootprints
import DitShim243.StateShift
import PipeLean_D234_SecpMulAlt_c19.DitBodyState
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
namespace PipeLean_D234_SecpMulAlt_c19.DitBodyExit

section Entry
variable (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (start : Nat) (imm : BitVec 26) (pins : HeapV2E17.Pins) (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (gt : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry start imm (BitVec.ofNat 64 pins.sp)) 4 = true)
    (rt : CheckedTopology.check raw (SecpRawDeployment.addresses EntryBinding.plan base entry) 4 = true)
    (info : Initial.Info EntryBinding.plan raw config rows mapping base (referenceImageI SecpArtifact.elf base (fun _ => 0))
      start imm 100 pins (DefaultState.capacity entry + 2) entry catalogue gt rt)
    (pre : Pre.ShimPreMG real 100 (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry start imm (BitVec.ofNat 64 pins.sp)) 4 gt)
      config rows mapping pins (Deployment.consumer EntryBinding.plan raw mapping base entry start imm (BitVec.ofNat 64 pins.sp))
      start (· ∈ codeOffsets (Deployment.extend EntryBinding.plan start imm)) (referenceImageI SecpArtifact.elf base (fun _ => 0)) base base
      (InitialCheck.runOffset EntryBinding.plan start 100 base entry) 112 catalogue (DefaultState.capacity entry+2) entry)
include info pre

theorem of_pre :
    DefaultCurrent.CurrentInv (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry start imm (BitVec.ofNat 64 pins.sp)) 4 gt)
      config rows mapping (Deployment.consumer EntryBinding.plan raw mapping base entry start imm (BitVec.ofNat 64 pins.sp))
      (· ∈ codeOffsets (Deployment.extend EntryBinding.plan start imm)) (referenceImageI SecpArtifact.elf base (fun _ => 0)) base base
      (InitialCheck.runOffset EntryBinding.plan start 100 base entry) 112 108 catalogue (stateAt real entry 108) ∧
    (stateAt real entry 108).regs.SP_EL0 = BitVec.ofNat 64 pins.sp ∧
    RtDit.Shim.SlotHas pins mapping (ArmCertMem.StpEval.stpData (stateAt real entry 3) 9#5 30#5) (stateAt real entry 108) ∧
    RtPremC.CtlRel (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry start imm (BitVec.ofNat 64 pins.sp)) 4 gt) entry (stateAt real entry 108) ∧
    (∃ used, ChoiceDelta entry (stateAt real entry 108) used ∧ used ≤ DefaultState.capacity entry+1) ∧
    (stateAt real entry 108).regs.PSTATE.DIT = 1#1 := by
  have pinsChecked : DataFrame.checkPins EntryBinding.plan = true := by decide
  have agree := DataTransport.of_pre real 100 _ config rows mapping pins _ start _ _ base base _ 112 _ (DefaultState.capacity entry+2) entry pre EntryBinding.plan pinsChecked
  obtain ⟨rt7,receipt⟩ := DitBodyEntry.of_pre real raw config rows mapping base start imm pins entry catalogue gt rt info pre
  obtain ⟨_,steps,invs,fin,last,finEq,ssa,frame,returned,used,delta,usedBound⟩ :=
    DitBodyRun.run real raw config rows mapping base (stateAt real entry 7) rt7 receipt
  have bodyControls := DitBodyFrames.preserves real raw config rows mapping base (stateAt real entry 7) rt7 receipt 101 (by decide)
  have shift := StateShift.stateAt_add real entry 7 101
  have final : fin = stateAt real entry 108 := finEq.trans shift.symm
  rw [final] at last ssa frame returned delta
  rw [← shift] at bodyControls
  have rawInv := invs 100 (by decide)
  have lr := DitBodyTerminal.original_lr mapping (stateAt real entry 7) _ rawInv.agrees
  have lr' : (stateAt real (stateAt real entry 7) 100).regs.gpr[30] = base + InitialCheck.runOffset EntryBinding.plan start 100 base entry 108 := by
    simpa only [show (GPRSummary.key (30#5).toNat).val = 30 by decide,entryGPR,dite_eq_left (show 30<31 by decide)] using lr.trans (by
      simpa only [entryGPR,dite_eq_left (show 30<31 by decide)] using pre.x30_7)
  have rawCurrent := CurrentBridge.of_core _ config rows mapping _ _ _ base base (offset EntryBinding.plan) 105 100
    catalogue (profile (stateAt real entry 7)) _ rawInv.core rawInv.branch
  have fetch := RawFetch.fetch _ config rows EntryBinding.plan raw mapping base (stateAt real entry 7) 105 rfl receipt.layout
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    100 _ rawInv.core (7044,0xd65f03c0) (List.mem_of_getElem? (show EntryBinding.plan.code[100]? = some (7044,0xd65f03c0) by rfl))
    (by rw [rawInv.core.v1.pc]; rfl)
  obtain ⟨other,actual,next,rest⟩ := DefaultHeapShimControl.shim_ret_between real _ config rows mapping _ _ _ base
    (fun o pa ho hm ht => receipt.layout.separated o pa ho hm (Or.inl ht))
    base (offset EntryBinding.plan) 105 100 catalogue
    (InitialCheck.runOffset EntryBinding.plan start 100 base entry) 112 108 (by decide) (by decide) receipt.page (by decide)
    info.metadata.nodup _ rawCurrent
    (by simpa only [show (GPRSummary.key (30#5).toNat).val = 30 by decide] using congrArg (fun v : BitVec 64 => v.toNat) lr ▸ receipt.low)
    lr' (by simpa only [show EntryBodyRet.W (30#5) = 0xd65f03c0#32 by decide] using fetch)
  have same : other = stateAt real entry 108 := by
    have eq := actual.symm.trans last
    cases eq
    rfl
  rw [same] at next
  have ctl : RtPremC.ctlv (stateAt real entry 108).regs = RtPremC.ctlv (stateAt real entry 7).regs := bodyControls.2.2
  have closed := ClosedTransport.closed pre.inv7.closed
    ((ClosedTransport.before_fetch _).trans (ctl.trans (ClosedTransport.before_fetch _).symm))
  have frameEntry : CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping entry)
      (stateAt real entry 7) (stateAt real entry 108) := by
    rw [← DataTransport.outputBytes agree]
    exact frame
  have placed := CurrentBridge.placed_frame _ _ base mapping _ _ _ pre.inv7.placed
    (fun o pa ho hm hout => info.layout.separated o pa ho hm (Or.inr hout)) frameEntry
  have current := CurrentBridge.expand raw _ _ 4 gt rt7 config rows mapping _ _ _ _ _ base base
    (InitialCheck.runOffset EntryBinding.plan start 100 base entry) 112 108 catalogue _ next closed placed
  have controls : RtPremC.CtlRel (CheckedTopology.spec raw (Deployment.addresses EntryBinding.plan base entry start imm (BitVec.ofNat 64 pins.sp)) 4 gt)
      (stateAt real entry 7) (stateAt real entry 108) :=
    ⟨ctl,fun pa ht => frame.writes pa (BodyFootprints.outside_table EntryBinding.plan raw mapping base _ receipt.layout pa ht)⟩
  have sp := DitBodyABI.preserved_of_agrees mapping (stateAt real entry 7) (stateAt real entry 108) ssa .sp (by decide)
  obtain ⟨preUsed,preDelta,preBound⟩ := pre.choice7
  refine ⟨current,sp.trans pre.sp7,?_,pre.control7.trans controls,?_,bodyControls.2.1.trans (pre.ditOn 7 (by decide) (by decide))⟩
  · intro n mapped i within
    exact (frameEntry.writes (n + i) (BodyFootprints.outside_slot EntryBinding.plan mapping entry pins info.slotRegions _ ⟨n,mapped,by omega,by omega⟩)).trans
      ((pre.mem47 (n + i)).trans (pre.slot4 n mapped i within))
  · refine ⟨preUsed + used,choice_delta_trans preDelta delta,?_⟩
    have capacityEq : DefaultState.capacity (stateAt real entry 7) = DefaultState.capacity entry := DataTransport.budget agree _
    omega

end Entry
#print axioms of_pre
end PipeLean_D234_SecpMulAlt_c19.DitBodyExit
