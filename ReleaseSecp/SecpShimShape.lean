import DitShim243.InitialCheck
import TranslateSpan.SecpEntryComponents
import SecpCallerContract

open Sail ArmFull ArmFull.Functions ArmCertWalk ArmCert.Translate.Model ArmBridge.Draft
open ArmBridge.CruxGenGuarded TranslateSpan TranslateSpan.SecpRawDeployment
open TranslateSpan.SecpEntryComponents DitShim243
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 4096

namespace ReleaseProfile.SecpShimCards

def Metadata (p : Plan) (raw : CheckedTopology.Raw) (base : BitVec 64)
    (start : Nat) (imm : BitVec 26) (L : Nat) (pins : HeapV2E17.Pins)
    (capacity : Nat) (e : NativeState) : Prop :=
  base.toNat % 4096 = 0 ∧ start % 4 = 0 ∧ InitialCheck.rawPC p % 4 = 0 ∧
  L + 1 = p.code.length ∧ (raw.logicalRows.map (·.logical)).Nodup ∧
  e.regs.SP_EL0 = BitVec.ofNat 64 pins.sp + 16#64 ∧ (BitVec.ofNat 64 pins.sp).toNat % 16 = 0 ∧
  2 ≤ capacity ∧ (entryGPR e 30).toNat < 2^55 ∧
  (base + Geometry.shimPC start 7).toNat < 2^55 ∧
  (base + InitialCheck.runOffset p start L base e 7).toNat < 2^55 ∧
  InitialCheck.runOffset p start L base e 6 + sign_extend (imm ++ 0#2) 64 =
    InitialCheck.runOffset p start L base e 7 ∧
  e.regs.FeatureImpl[103]! = true ∧ e.regs.FeatureImpl[123]! = true ∧
  e.regs.FeatureImpl[227]! = false ∧ e.regs.FeatureImpl[2]! = false ∧
  e.regs.FeatureImpl[3]! = false ∧ e.regs.FeatureImpl[6]! = true ∧
  e.regs.FeatureImpl[7]! = true ∧ e.regs.FeatureImpl[230]! = false ∧
  RtBl.CallerInv.CallerResidue e

theorem metadata_iff (p : Plan) (raw : CheckedTopology.Raw) (base : BitVec 64)
    (start : Nat) (imm : BitVec 26) (L : Nat) (pins : HeapV2E17.Pins)
    (capacity : Nat) (entry : NativeState) :
    InitialCheck.checkMetadata p raw base start imm L pins capacity entry = true ↔
      Metadata p raw base start imm L pins capacity entry := by
  simp only [InitialCheck.checkMetadata,Metadata,decide_eq_true_eq]

def Fields {globalDomain bodyDomain : QueryDomain}
    (globalSpec : TopologyImageSpec globalDomain) (bodySpec : TopologyImageSpec bodyDomain)
    (p : Plan) (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (image : MemReloc.Image)
    (start : Nat) (imm : BitVec 26) (L : Nat) (pins : HeapV2E17.Pins)
    (capacity : Nat) (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) : Prop :=
  Metadata p raw base start imm L pins capacity entry ∧
  controlsLeaves globalSpec config rows (profile entry) catalogue
    (base + InitialCheck.runOffset p start L base entry 0) (L+12) entry ∧
  MachineEntry.checkPlaced (codeOffsets (Deployment.extend p start imm)) image base mapping entry = true ∧
  CheckedEntry.checkQueries globalSpec config rows mapping 1030
    (Deployment.selectedQueries p base entry start imm (BitVec.ofNat 64 pins.sp)) 4
    (beforeFetchState entry) = true ∧
  CheckedEntry.checkQueries bodySpec config rows mapping 1030 (queries p base entry) 4
    (beforeFetchState entry) = true ∧
  MachineEntry.checkPresent p.regions (view p mapping entry) entry = true ∧
  checkLayout (Deployment.extend p start imm) raw mapping base entry = true ∧
  SlotCheck.check pins mapping (rowsFootprint raw.imageRows) entry = true ∧
  StaticLayout.checkCodeAvoid (codeOffsets (Deployment.extend p start imm)) mapping base
    (SlotCheck.slotByte pins mapping) = true ∧
  SlotCheck.checkRegions pins mapping (view p mapping entry) (p.buffers ++ p.outputs) = true ∧
  InitialCheck.checkWords image start imm = true ∧
  branchLeaves entry ∧ branchExtrasLeaves entry ∧
  (sites p entry).all (fun site => SelectedLoadFacts.checkTargets mapping site.address) = true ∧
  TagStatusRows.check capacity entry = true

theorem check_iff (p : Plan) (raw : CheckedTopology.Raw) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (image : MemReloc.Image) (start : Nat) (imm : BitVec 26) (L : Nat)
    (pins : HeapV2E17.Pins) (capacity : Nat) (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) :
    InitialCheck.check p raw config rows mapping base image start imm L pins capacity entry catalogue = true ↔
      ∃ gt : CheckedTopology.check raw
          (Deployment.addresses p base entry start imm (BitVec.ofNat 64 pins.sp)) 4 = true,
      ∃ rt : CheckedTopology.check raw (addresses p base entry) 4 = true,
        Fields (CheckedTopology.spec raw
          (Deployment.addresses p base entry start imm (BitVec.ofNat 64 pins.sp)) 4 gt)
          (CheckedTopology.spec raw (addresses p base entry) 4 rt)
          p raw config rows mapping base image start imm L pins capacity entry catalogue := by
  constructor
  · intro checked
    obtain ⟨gt,rt,c⟩ := InitialCheck.of_check p raw config rows mapping base image
      start imm L pins capacity entry catalogue checked
    refine ⟨gt,rt,(metadata_iff p raw base start imm L pins capacity entry).mp c.metadata,
      ?_,c.placed,c.globalQueries,c.rawQueries,c.present,c.layout,c.slots,c.slotCode,
      c.slotRegions,c.words,(branch_iff entry).mp c.branch,
      (branchExtras_iff entry).mp c.branchExtras,c.targets,c.status⟩
    exact (controls_iff _ config rows (profile entry) catalogue
      (base + InitialCheck.runOffset p start L base entry 0) (L+12) entry).mp c.controls
  · rintro ⟨gt,rt,f⟩
    rcases f with ⟨metadata,controls,placed,globalQueries,rawQueries,present,layout,
      slots,slotCode,slotRegions,words,branch,extras,targets,status⟩
    unfold InitialCheck.check
    rw [dite_eq_left gt,dite_eq_left rt]
    simp only [InitialCheck.components,List.all_cons,List.all_nil,id,Bool.and_eq_true,
      and_true]
    exact ⟨(metadata_iff p raw base start imm L pins capacity entry).mpr metadata,
      (controls_iff _ config rows (profile entry) catalogue
        (base + InitialCheck.runOffset p start L base entry 0) (L+12) entry).mpr controls,
      placed,globalQueries,rawQueries,present,layout,slots,slotCode,slotRegions,words,
      (branch_iff entry).mpr branch,(branchExtras_iff entry).mpr extras,targets,status⟩

theorem caller_of_fields {globalDomain bodyDomain : QueryDomain}
    (globalSpec : TopologyImageSpec globalDomain) (bodySpec : TopologyImageSpec bodyDomain)
    (p : Plan) (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (image : MemReloc.Image)
    (start : Nat) (imm : BitVec 26) (L : Nat) (pins : HeapV2E17.Pins)
    (capacity : Nat) (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (fields : Fields globalSpec bodySpec p raw config rows mapping base image start imm L pins capacity entry catalogue) :
    SecpCaller.Contract (SecpCaller.objects p entry) := by
  rcases fields with ⟨_,_,_,_,_,_,layout,_⟩
  simp only [checkLayout,Bool.and_eq_true] at layout
  exact SecpCaller.of_checkBuffers p raw entry layout.1.1.1.1.1

#print axioms metadata_iff
#print axioms check_iff
#print axioms caller_of_fields
end ReleaseProfile.SecpShimCards
