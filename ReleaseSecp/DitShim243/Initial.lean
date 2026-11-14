import DitShim243.InitialCheck
import DitShim243.TopologyTransport
import DefaultCurrent
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open TranslateSpan TranslateSpan.SecpRawDeployment HeapV2StepCerts NativeMteTagCheck ReleaseProfile ArmCertValue ArmCertPipe
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace DitShim243.Initial

structure Metadata (p : Plan) (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (image : MemReloc.Image)
    (start : Nat) (imm : BitVec 26) (L : Nat) (pins : HeapV2E17.Pins) (capacity : Nat) (entry : NativeState) : Prop where
  page : base.toNat % 4096 = 0
  startAligned : start % 4 = 0
  bodyAligned : InitialCheck.rawPC p % 4 = 0
  length : L + 1 = p.code.length
  nodup : (raw.logicalRows.map (·.logical)).Nodup
  sp : entry.regs.SP_EL0 = BitVec.ofNat 64 pins.sp + 16#64
  slotAligned : (BitVec.ofNat 64 pins.sp).toNat % 16 = 0
  rowRoom : 2 ≤ capacity
  returnLow : (entryGPR entry 30).toNat < 2^55
  continuationLow : (base + Geometry.shimPC start 7).toNat < 2^55
  bodyLow : (base + InitialCheck.runOffset p start L base entry 7).toNat < 2^55
  land : InitialCheck.runOffset p start L base entry 6 + sign_extend (imm ++ 0#2) 64 = InitialCheck.runOffset p start L base entry 7
  mrs : NativeEntryAdapters.MrsDit.Profile entry
  isb : NativeEntryAdapters.IsbSy.Profile entry
  residue : RtBl.CallerInv.CallerResidue entry

theorem metadata_of_check (p : Plan) (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (image : MemReloc.Image)
    (start : Nat) (imm : BitVec 26) (L : Nat) (pins : HeapV2E17.Pins) (capacity : Nat) (entry : NativeState)
    (checked : InitialCheck.checkMetadata p raw base start imm L pins capacity entry = true) : Metadata p raw config rows mapping base image start imm L pins capacity entry := by
  obtain ⟨page,sa,ba,len,nd,sp,al,room,ret,cont,body,land,f103,f123,f227,f2,f3,f6,f7,f230,residue⟩ := of_decide_eq_true checked
  exact ⟨page,sa,ba,len,nd,sp,al,room,ret,cont,body,land,⟨f103,f123,f227⟩,⟨f2,f3,f6,f7,f230⟩,residue⟩

structure Info (p : Plan) (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (image : MemReloc.Image)
    (start : Nat) (imm : BitVec 26) (L : Nat) (pins : HeapV2E17.Pins) (capacity : Nat) (entry : NativeState) (catalogue : ControlCatalogue)
    (globalTopology : CheckedTopology.check raw (Deployment.addresses p base entry start imm (BitVec.ofNat 64 pins.sp)) 4 = true)
    (rawTopology : CheckedTopology.check raw (SecpRawDeployment.addresses p base entry) 4 = true) : Prop where
  metadata : Metadata p raw config rows mapping base image start imm L pins capacity entry
  current : DefaultCurrent.CurrentInv (CheckedTopology.spec raw (Deployment.addresses p base entry start imm (BitVec.ofNat 64 pins.sp)) 4 globalTopology) config rows mapping (Deployment.consumer p raw mapping base entry start imm (BitVec.ofNat 64 pins.sp))
    (· ∈ (codeOffsets (Deployment.extend p start imm))) image base base (InitialCheck.runOffset p start L base entry) (L+12) 0 catalogue entry
  profileAt : NativeAccess.ProfileAt (profile entry) entry
  rawCurrent : CurrentS1At (CheckedTopology.spec raw (SecpRawDeployment.addresses p base entry) 4 rawTopology) config rows (beforeFetchState entry)
  rawClosed : ClosedMembershipAt (CheckedTopology.spec raw (SecpRawDeployment.addresses p base entry) 4 rawTopology) config rows mapping (SecpRawDeployment.consumer p raw mapping base entry) (beforeFetchState entry)
  rawLayout : LayoutFacts p raw mapping base entry
  layout : LayoutFacts (Deployment.extend p start imm) raw mapping base entry
  present : ∀ g j i k, memBL p.regions 0 g j = some (i,k) → (Physical.regionByte (view p mapping entry) entry g j).isSome = true
  spans : ∀ (r : Region) (n word : Nat), (r,n) ∈ p.buffers → p.normalize r = r → 8*word+16 ≤ n →
    SelectedBinding.At (view p mapping entry) r word mapping (regionVA entry r (8*word))
  slots : RtShim.SlotPrem.ShimSlotStatic pins mapping (rowsFootprint raw.imageRows)
  slotPresent : RtShim.SlotPrem.ShimSlotPresent pins mapping entry
  code : Fetch.CodeFacts (CheckedTopology.spec raw (Deployment.addresses p base entry start imm (BitVec.ofNat 64 pins.sp)) 4 globalTopology) mapping (Deployment.consumer p raw mapping base entry start imm (BitVec.ofNat 64 pins.sp)) (· ∈ (codeOffsets (Deployment.extend p start imm))) image base start (Fetches.word imm)
  codeSlot : ImageTableSeparated (· ∈ (codeOffsets (Deployment.extend p start imm))) base mapping (RtShim2.ShimMem.slotBytes pins mapping)
  slotRegions : ∀ r n, (r,n) ∈ p.buffers ++ p.outputs → ∀ i < n, ∀ pa,
    view p mapping entry r i = some pa → ¬ RtShim2.ShimMem.slotBytes pins mapping pa
  targets : ∀ site ∈ sites p entry, SelectedLoadFacts.checkTargets mapping site.address = true
  status : TagStatusRows entry (entry.choiceOcc.getD 1354 0) capacity

theorem of_conditions (p : Plan) (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (image : MemReloc.Image)
    (start : Nat) (imm : BitVec 26) (L : Nat) (pins : HeapV2E17.Pins) (capacity : Nat) (entry : NativeState) (catalogue : ControlCatalogue)
    (globalTopology : CheckedTopology.check raw (Deployment.addresses p base entry start imm (BitVec.ofNat 64 pins.sp)) 4 = true)
    (rawTopology : CheckedTopology.check raw (SecpRawDeployment.addresses p base entry) 4 = true)
    (checked : InitialCheck.Conditions p raw config rows mapping base image start imm L pins capacity entry catalogue globalTopology rawTopology) :
    Info p raw config rows mapping base image start imm L pins capacity entry catalogue globalTopology rawTopology := by
  let G := (CheckedTopology.spec raw (Deployment.addresses p base entry start imm (BitVec.ofNat 64 pins.sp)) 4 globalTopology)
  let R := (CheckedTopology.spec raw (SecpRawDeployment.addresses p base entry) 4 rawTopology)
  let M := (Deployment.consumer p raw mapping base entry start imm (BitVec.ofNat 64 pins.sp))
  let offsets := (codeOffsets (Deployment.extend p start imm))
  let off := (InitialCheck.runOffset p start L base entry)
  have closed : ClosedMembershipAt G config rows mapping M (beforeFetchState entry) := by
    apply CheckedEntry.closed_selected (· ∈ (Deployment.addresses p base entry start imm (BitVec.ofNat 64 pins.sp))) G config rows mapping (rowsFootprint raw.imageRows).byte
      (Deployment.allSites p entry (BitVec.ofNat 64 pins.sp)) (codeVAs (Deployment.extend p start imm) base) 1030 4 (beforeFetchState entry) ?_ checked.globalQueries
    intro q member
    exact List.mem_map.mpr ⟨q,List.mem_append_left _ member,rfl⟩
  have core := DefaultMTE2.core_of_checks G config rows (profile entry) catalogue
    mapping M offsets image base off (L+12) entry checked.controls checked.placed closed
  have branch := BranchEntryMTE2.pins_of_check entry core.v1.features checked.branch checked.branchExtras
  have current : DefaultCurrent.CurrentInv G config rows mapping M (· ∈ offsets) image base base off (L+12) 0 catalogue entry :=
    ⟨core.v1,core.closed,core.placed,branch,core.raw,core.noUpd,core.post,core.mode,core.debug,core.feat,core.dcache,core.controls⟩
  have rawCurrent := TopologyTransport.current raw (Deployment.addresses p base entry start imm (BitVec.ofNat 64 pins.sp)) (SecpRawDeployment.addresses p base entry) 4 globalTopology rawTopology config rows (beforeFetchState entry) current.v1.current
  have rawClosed : ClosedMembershipAt R config rows mapping (SecpRawDeployment.consumer p raw mapping base entry) (beforeFetchState entry) := by
    have selected := EntryMatrix.checked_prefix checked.rawQueries
    apply CheckedEntry.closed_selected (· ∈ (SecpRawDeployment.addresses p base entry)) R config rows mapping (rowsFootprint raw.imageRows).byte
      (sites p entry) (codeVAs p base) 1030 4 (beforeFetchState entry) ?_ selected
    intro q member
    exact List.mem_map.mpr ⟨q,List.mem_append_left _ member,rfl⟩
  have layout := layout_of_check (Deployment.extend p start imm) raw mapping base entry checked.layout
  have slots := SlotCheck.of_check pins mapping (rowsFootprint raw.imageRows) entry checked.slots
  have imageWord : ∀ j, j < 11 → ∀ i < 4, image (start+4 * j + i) = some ((Fetches.word imm j).extractLsb' (8 * i) 8) := by
    intro j hj i hi
    exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp checked.words j (List.mem_range.mpr hj)) i (List.mem_range.mpr hi))
  have code := DeploymentFacts.code_facts G p raw mapping base entry start imm (BitVec.ofNat 64 pins.sp) image rfl layout imageWord
  have codeSlot := StaticLayout.code_avoid_of_check offsets mapping base (SlotCheck.slotByte pins mapping)
    (RtShim2.ShimMem.slotBytes pins mapping) (fun pa inside => (SlotCheck.slotByte_true pins mapping pa).mpr inside) checked.slotCode
  exact ⟨metadata_of_check p raw config rows mapping base image start imm L pins capacity entry checked.metadata,current,core.profileAt,rawCurrent,rawClosed,
    DeploymentFacts.raw_layout p raw mapping base entry start imm layout,layout,
    MachineEntry.present_of_check p.regions (view p mapping entry) entry checked.present,
    SecpCurrentEntry.span R config rows p mapping base entry rawCurrent checked.rawQueries,
    slots.1,slots.2,code,codeSlot,SlotCheck.regions_of_check pins mapping (view p mapping entry) (p.buffers ++ p.outputs) checked.slotRegions,
    List.all_eq_true.mp checked.targets,TagStatusRows.of_check capacity entry checked.status⟩

#print axioms metadata_of_check
#print axioms of_conditions
end DitShim243.Initial
