import DitShim243.DeploymentFacts
import DitShim243.CallerOffset
import DitShim243.SlotCheck
import DitShim243.Profiles
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open TranslateSpan TranslateSpan.SecpRawDeployment HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace DitShim243.InitialCheck

instance callerResidueDecidable (s : NativeState) : Decidable (RtBl.CallerInv.CallerResidue s) :=
  inferInstanceAs (Decidable (_get_SCR_EL3_Type_GCSEn (s.regs.bank_BitVec_64 .SCR_EL3) = 0#1))

def rawPC (p : Plan) : Nat := ((p.code[0]?).getD (0,0)).1

def runOffset (p : Plan) (start L : Nat) (base : BitVec 64) (entry : NativeState) : Nat → BitVec 64 :=
  Geometry.wholeOffset start (rawPC p) L base (entryGPR entry 30)

def checkMetadata (p : Plan) (raw : CheckedTopology.Raw) (base : BitVec 64)
    (start : Nat) (imm : BitVec 26) (L : Nat) (pins : HeapV2E17.Pins) (capacity : Nat) (e : NativeState) : Bool :=
  decide (base.toNat % 4096 = 0 ∧ start % 4 = 0 ∧ rawPC p % 4 = 0 ∧ L + 1 = p.code.length ∧
    (raw.logicalRows.map (·.logical)).Nodup ∧
    e.regs.SP_EL0 = BitVec.ofNat 64 pins.sp + 16#64 ∧ (BitVec.ofNat 64 pins.sp).toNat % 16 = 0 ∧
    2 ≤ capacity ∧ (entryGPR e 30).toNat < 2^55 ∧
    (base + Geometry.shimPC start 7).toNat < 2^55 ∧ (base + runOffset p start L base e 7).toNat < 2^55 ∧
    runOffset p start L base e 6 + sign_extend (imm ++ 0#2) 64 = runOffset p start L base e 7 ∧
    e.regs.FeatureImpl[103]! = true ∧ e.regs.FeatureImpl[123]! = true ∧ e.regs.FeatureImpl[227]! = false ∧
    e.regs.FeatureImpl[2]! = false ∧ e.regs.FeatureImpl[3]! = false ∧ e.regs.FeatureImpl[6]! = true ∧
    e.regs.FeatureImpl[7]! = true ∧ e.regs.FeatureImpl[230]! = false ∧ RtBl.CallerInv.CallerResidue e)

def checkWords (image : MemReloc.Image) (start : Nat) (imm : BitVec 26) : Bool :=
  (List.range 11).all fun j => (List.range 4).all fun i =>
    image (start + 4 * j + i) == some ((Fetches.word imm j).extractLsb' (8 * i) 8)

def components (p : Plan) (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (image : MemReloc.Image)
    (start : Nat) (imm : BitVec 26) (L : Nat) (pins : HeapV2E17.Pins) (capacity : Nat) (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (globalTopology : CheckedTopology.check raw (Deployment.addresses p base entry start imm (BitVec.ofNat 64 pins.sp)) 4 = true)
    (rawTopology : CheckedTopology.check raw (SecpRawDeployment.addresses p base entry) 4 = true) : List Bool :=
  [checkMetadata p raw base start imm L pins capacity entry,
   DefaultMTE2.checkControls (CheckedTopology.spec raw (Deployment.addresses p base entry start imm (BitVec.ofNat 64 pins.sp)) 4 globalTopology) config rows (profile entry) catalogue (base + (runOffset p start L base entry) 0) (L + 12) entry,
   MachineEntry.checkPlaced (codeOffsets (Deployment.extend p start imm)) image base mapping entry,
   CheckedEntry.checkQueries (CheckedTopology.spec raw (Deployment.addresses p base entry start imm (BitVec.ofNat 64 pins.sp)) 4 globalTopology) config rows mapping 1030 (Deployment.selectedQueries p base entry start imm (BitVec.ofNat 64 pins.sp)) 4 (beforeFetchState entry),
   CheckedEntry.checkQueries (CheckedTopology.spec raw (SecpRawDeployment.addresses p base entry) 4 rawTopology) config rows mapping 1030 (SecpRawDeployment.queries p base entry) 4 (beforeFetchState entry),
   MachineEntry.checkPresent p.regions (view p mapping entry) entry,
   checkLayout (Deployment.extend p start imm) raw mapping base entry,
   SlotCheck.check pins mapping (rowsFootprint raw.imageRows) entry,
   StaticLayout.checkCodeAvoid (codeOffsets (Deployment.extend p start imm)) mapping base (SlotCheck.slotByte pins mapping),
   SlotCheck.checkRegions pins mapping (view p mapping entry) (p.buffers ++ p.outputs),
   checkWords image start imm,
   BranchEntryMTE2.check entry,
   EntryControls.checkBranchExtras entry,
   (sites p entry).all (fun site => SelectedLoadFacts.checkTargets mapping site.address),
   TagStatusRows.check capacity entry]

structure Conditions (p : Plan) (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (image : MemReloc.Image)
    (start : Nat) (imm : BitVec 26) (L : Nat) (pins : HeapV2E17.Pins) (capacity : Nat) (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (globalTopology : CheckedTopology.check raw (Deployment.addresses p base entry start imm (BitVec.ofNat 64 pins.sp)) 4 = true)
    (rawTopology : CheckedTopology.check raw (SecpRawDeployment.addresses p base entry) 4 = true) : Prop where
  metadata : (checkMetadata p raw base start imm L pins capacity entry) = true
  controls : (DefaultMTE2.checkControls (CheckedTopology.spec raw (Deployment.addresses p base entry start imm (BitVec.ofNat 64 pins.sp)) 4 globalTopology) config rows (profile entry) catalogue (base + (runOffset p start L base entry) 0) (L + 12) entry) = true
  placed : (MachineEntry.checkPlaced (codeOffsets (Deployment.extend p start imm)) image base mapping entry) = true
  globalQueries : (CheckedEntry.checkQueries (CheckedTopology.spec raw (Deployment.addresses p base entry start imm (BitVec.ofNat 64 pins.sp)) 4 globalTopology) config rows mapping 1030 (Deployment.selectedQueries p base entry start imm (BitVec.ofNat 64 pins.sp)) 4 (beforeFetchState entry)) = true
  rawQueries : (CheckedEntry.checkQueries (CheckedTopology.spec raw (SecpRawDeployment.addresses p base entry) 4 rawTopology) config rows mapping 1030 (SecpRawDeployment.queries p base entry) 4 (beforeFetchState entry)) = true
  present : (MachineEntry.checkPresent p.regions (view p mapping entry) entry) = true
  layout : (checkLayout (Deployment.extend p start imm) raw mapping base entry) = true
  slots : (SlotCheck.check pins mapping (rowsFootprint raw.imageRows) entry) = true
  slotCode : (StaticLayout.checkCodeAvoid (codeOffsets (Deployment.extend p start imm)) mapping base (SlotCheck.slotByte pins mapping)) = true
  slotRegions : (SlotCheck.checkRegions pins mapping (view p mapping entry) (p.buffers ++ p.outputs)) = true
  words : (checkWords image start imm) = true
  branch : (BranchEntryMTE2.check entry) = true
  branchExtras : (EntryControls.checkBranchExtras entry) = true
  targets : ((sites p entry).all (fun site => SelectedLoadFacts.checkTargets mapping site.address)) = true
  status : (TagStatusRows.check capacity entry) = true

def check (p : Plan) (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (image : MemReloc.Image)
    (start : Nat) (imm : BitVec 26) (L : Nat) (pins : HeapV2E17.Pins) (capacity : Nat) (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) : Bool :=
  if globalTopology : CheckedTopology.check raw (Deployment.addresses p base entry start imm (BitVec.ofNat 64 pins.sp)) 4 = true then
    if rawTopology : CheckedTopology.check raw (SecpRawDeployment.addresses p base entry) 4 = true then
      (components p raw config rows mapping base image start imm L pins capacity entry catalogue globalTopology rawTopology).all id
    else false
  else false

theorem of_check (p : Plan) (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (image : MemReloc.Image)
    (start : Nat) (imm : BitVec 26) (L : Nat) (pins : HeapV2E17.Pins) (capacity : Nat) (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (checked : check p raw config rows mapping base image start imm L pins capacity entry catalogue = true) :
    ∃ globalTopology : CheckedTopology.check raw (Deployment.addresses p base entry start imm (BitVec.ofNat 64 pins.sp)) 4 = true,
      ∃ rawTopology : CheckedTopology.check raw (SecpRawDeployment.addresses p base entry) 4 = true,
        Conditions p raw config rows mapping base image start imm L pins capacity entry catalogue globalTopology rawTopology := by
  unfold check at checked
  split at checked
  · rename_i globalTopology
    split at checked
    · rename_i rawTopology
      refine ⟨globalTopology,rawTopology,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · exact List.all_eq_true.mp checked _ (List.mem_of_getElem? (show (components p raw config rows mapping base image start imm L pins capacity entry catalogue globalTopology rawTopology)[0]? = some (checkMetadata p raw base start imm L pins capacity entry) from rfl))
      · exact List.all_eq_true.mp checked _ (List.mem_of_getElem? (show (components p raw config rows mapping base image start imm L pins capacity entry catalogue globalTopology rawTopology)[1]? = some (DefaultMTE2.checkControls (CheckedTopology.spec raw (Deployment.addresses p base entry start imm (BitVec.ofNat 64 pins.sp)) 4 globalTopology) config rows (profile entry) catalogue (base + (runOffset p start L base entry) 0) (L + 12) entry) from rfl))
      · exact List.all_eq_true.mp checked _ (List.mem_of_getElem? (show (components p raw config rows mapping base image start imm L pins capacity entry catalogue globalTopology rawTopology)[2]? = some (MachineEntry.checkPlaced (codeOffsets (Deployment.extend p start imm)) image base mapping entry) from rfl))
      · exact List.all_eq_true.mp checked _ (List.mem_of_getElem? (show (components p raw config rows mapping base image start imm L pins capacity entry catalogue globalTopology rawTopology)[3]? = some (CheckedEntry.checkQueries (CheckedTopology.spec raw (Deployment.addresses p base entry start imm (BitVec.ofNat 64 pins.sp)) 4 globalTopology) config rows mapping 1030 (Deployment.selectedQueries p base entry start imm (BitVec.ofNat 64 pins.sp)) 4 (beforeFetchState entry)) from rfl))
      · exact List.all_eq_true.mp checked _ (List.mem_of_getElem? (show (components p raw config rows mapping base image start imm L pins capacity entry catalogue globalTopology rawTopology)[4]? = some (CheckedEntry.checkQueries (CheckedTopology.spec raw (SecpRawDeployment.addresses p base entry) 4 rawTopology) config rows mapping 1030 (SecpRawDeployment.queries p base entry) 4 (beforeFetchState entry)) from rfl))
      · exact List.all_eq_true.mp checked _ (List.mem_of_getElem? (show (components p raw config rows mapping base image start imm L pins capacity entry catalogue globalTopology rawTopology)[5]? = some (MachineEntry.checkPresent p.regions (view p mapping entry) entry) from rfl))
      · exact List.all_eq_true.mp checked _ (List.mem_of_getElem? (show (components p raw config rows mapping base image start imm L pins capacity entry catalogue globalTopology rawTopology)[6]? = some (checkLayout (Deployment.extend p start imm) raw mapping base entry) from rfl))
      · exact List.all_eq_true.mp checked _ (List.mem_of_getElem? (show (components p raw config rows mapping base image start imm L pins capacity entry catalogue globalTopology rawTopology)[7]? = some (SlotCheck.check pins mapping (rowsFootprint raw.imageRows) entry) from rfl))
      · exact List.all_eq_true.mp checked _ (List.mem_of_getElem? (show (components p raw config rows mapping base image start imm L pins capacity entry catalogue globalTopology rawTopology)[8]? = some (StaticLayout.checkCodeAvoid (codeOffsets (Deployment.extend p start imm)) mapping base (SlotCheck.slotByte pins mapping)) from rfl))
      · exact List.all_eq_true.mp checked _ (List.mem_of_getElem? (show (components p raw config rows mapping base image start imm L pins capacity entry catalogue globalTopology rawTopology)[9]? = some (SlotCheck.checkRegions pins mapping (view p mapping entry) (p.buffers ++ p.outputs)) from rfl))
      · exact List.all_eq_true.mp checked _ (List.mem_of_getElem? (show (components p raw config rows mapping base image start imm L pins capacity entry catalogue globalTopology rawTopology)[10]? = some (checkWords image start imm) from rfl))
      · exact List.all_eq_true.mp checked _ (List.mem_of_getElem? (show (components p raw config rows mapping base image start imm L pins capacity entry catalogue globalTopology rawTopology)[11]? = some (BranchEntryMTE2.check entry) from rfl))
      · exact List.all_eq_true.mp checked _ (List.mem_of_getElem? (show (components p raw config rows mapping base image start imm L pins capacity entry catalogue globalTopology rawTopology)[12]? = some (EntryControls.checkBranchExtras entry) from rfl))
      · exact List.all_eq_true.mp checked _ (List.mem_of_getElem? (show (components p raw config rows mapping base image start imm L pins capacity entry catalogue globalTopology rawTopology)[13]? = some ((sites p entry).all (fun site => SelectedLoadFacts.checkTargets mapping site.address)) from rfl))
      · exact List.all_eq_true.mp checked _ (List.mem_of_getElem? (show (components p raw config rows mapping base image start imm L pins capacity entry catalogue globalTopology rawTopology)[14]? = some (TagStatusRows.check capacity entry) from rfl))
    · contradiction
  · contradiction

#print axioms of_check
end DitShim243.InitialCheck
