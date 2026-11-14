import TranslateSpan.SecpCurrentEntry
import TranslateSpan.DefaultContext
import TranslateSpan.TagStatusRows
import ArmCertPipe.ValuePlan

open Sail ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ArmBridge.Draft
open ArmBridge.CruxGenGuarded NativeAccess ArmCertValue ArmCertPipe
open ArmBridge.CruxGenGuarded.ChainInv
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace TranslateSpan.SecpDefaultEntry
open SecpRawDeployment

def checkRaw (p : Plan) (image : MemReloc.Image) (raw : CheckedTopology.Raw)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) : Bool :=
  if topology : CheckedTopology.check raw (addresses p base entry) 4 = true then
    let spec := CheckedTopology.spec raw (addresses p base entry) 4 topology
    DefaultMTE2.checkControls spec config rows (profile entry) catalogue (base + offset p 0) p.code.length entry &&
      MachineEntry.checkPlaced (codeOffsets p) image base mapping entry &&
      MachineEntry.checkPresent p.regions (view p mapping entry) entry &&
      CheckedEntry.checkQueries spec config rows mapping 1030 (queries p base entry) 4 (beforeFetchState entry) &&
      checkLayout p raw mapping base entry
  else false

theorem raw_of_check (p : Plan) (image : MemReloc.Image) (raw : CheckedTopology.Raw)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (entry : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (checked : checkRaw p image raw config rows mapping base entry catalogue = true) :
    ∃ topology : CheckedTopology.check raw (addresses p base entry) 4 = true,
      DefaultMTE2.Core (CheckedTopology.spec raw (addresses p base entry) 4 topology)
        config rows mapping (consumer p raw mapping base entry) (· ∈ codeOffsets p) image
        base base (offset p) p.code.length (profile entry) catalogue 0 entry ∧
      LayoutFacts p raw mapping base entry ∧
      CheckedEntry.checkQueries (CheckedTopology.spec raw (addresses p base entry) 4 topology)
        config rows mapping 1030 (queries p base entry) 4 (beforeFetchState entry) = true ∧
      (∀ g j i k, memBL p.regions 0 g j = some (i,k) →
        (Physical.regionByte (view p mapping entry) entry g j).isSome = true) := by
  unfold checkRaw at checked
  split at checked
  · rename_i topology
    simp only [Bool.and_eq_true] at checked
    obtain ⟨⟨⟨⟨controls, placed⟩, present⟩, current⟩, layout⟩ := checked
    let spec := CheckedTopology.spec raw (addresses p base entry) 4 topology
    have selected := EntryMatrix.checked_prefix current
    have closed := CheckedEntry.closed_selected (· ∈ addresses p base entry) spec config rows
      mapping (rowsFootprint raw.imageRows).byte (sites p entry) (codeVAs p base) 1030 4
      (beforeFetchState entry)
      (fun q member => List.mem_map.mpr ⟨q, List.mem_append_left _ member, rfl⟩) selected
    exact ⟨topology, DefaultMTE2.core_of_checks spec config rows (profile entry) catalogue
      mapping (consumer p raw mapping base entry) (codeOffsets p) image base (offset p)
      p.code.length entry controls placed closed, layout_of_check p raw mapping base entry layout, current,
      MachineEntry.present_of_check p.regions (view p mapping entry) entry present⟩
  · contradiction

def fetch {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (p : Plan) (raw : CheckedTopology.Raw)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (table : spec.imageRows = raw.imageRows) (layout : LayoutFacts p raw mapping base entry)
    (image : MemReloc.Image)
    (imageWords : ∀ c ∈ p.code, ∀ i < 4, image (c.1 + i) =
      some ((BitVec.ofNat 32 c.2).extractLsb' (8 * i) 8))
    (k : Nat) (x : NativeState)
    (inv : DefaultMTE2.Core spec config rows mapping (consumer p raw mapping base entry)
      (· ∈ codeOffsets p) image base base (offset p) p.code.length (profile entry) catalogue k x)
    (c : Nat × Nat) (member : c ∈ p.code)
    (pc : x.regs._PC = MemReloc.imageAddress base c.1) :
    FetchObligations spec config rows mapping (BitVec.ofNat 32 c.2) x := by
  have separated : ImageTableSeparated (· ∈ codeOffsets p) base mapping
      (rowsFootprint spec.imageRows).byte := by
    rw [table]
    intro o pa inside mapped inTable
    exact layout.separated o pa inside mapped (Or.inl inTable)
  refine CurrentMTE2.fetchG spec config rows mapping (consumer p raw mapping base entry)
    (· ∈ codeOffsets p) image base base (offset p) p.code.length k x
    inv.v1 inv.closed inv.placed c.1 (BitVec.ofNat 32 c.2) pc ?_
    (layout.codeWords c member).1 (layout.codeWords c member).2 separated
    (imageWords c member) ?_
  · intro i bound
    change c.1 + i ∈ p.code.flatMap (fun w => (List.range 4).map (w.1 + ·))
    exact List.mem_flatMap.mpr ⟨c, member, List.mem_map.mpr ⟨i, List.mem_range.mpr bound, rfl⟩⟩
  · intro acc shape
    rw [pc]
    exact SelectedMap.fetch_member (sites p entry) (codeVAs p base) mapping
      (rowsFootprint raw.imageRows).byte _ acc
      (List.mem_map.mpr ⟨c, member, rfl⟩) shape

def check (p : Plan) (image : MemReloc.Image) (raw : CheckedTopology.Raw)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (capacity : Nat) (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) : Bool :=
  checkRaw p image raw config rows mapping base entry catalogue &&
    BranchEntryMTE2.check entry && EntryControls.checkBranchExtras entry &&
    decide (base.toNat % 4096 = 0 ∧ (entryGPR entry 30).toNat < 2 ^ 55) &&
    (sites p entry).all (fun site => SelectedLoadFacts.checkTargets mapping site.address) &&
    TagStatusRows.check capacity entry

theorem of_check (p : Plan) (image : MemReloc.Image) (raw : CheckedTopology.Raw)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (capacity : Nat) (entry : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (language : ValuePlan.Language) (regions : List Region) (plan : List (ValuePlan.Step language))
    (checked : check p image raw config rows mapping base capacity entry catalogue = true) :
    ∃ topology : CheckedTopology.check raw (addresses p base entry) 4 = true,
      DefaultMTE2.Core (CheckedTopology.spec raw (addresses p base entry) 4 topology)
        config rows mapping (consumer p raw mapping base entry) (· ∈ codeOffsets p) image
        base base (offset p) p.code.length (profile entry) catalogue 0 entry ∧
      BranchMTE2.Pins entry ∧
      ValuePlan.AgreesAt language (view p mapping entry) regions (σ0L p.regions)
        (SecpCurrentEntry.inputs p mapping entry) plan 0 entry ∧
      LayoutFacts p raw mapping base entry ∧
      base.toNat % 4096 = 0 ∧ (entryGPR entry 30).toNat < 2 ^ 55 ∧
      (∀ site ∈ sites p entry, SelectedLoadFacts.checkTargets mapping site.address = true) ∧
      CheckedEntry.checkQueries (CheckedTopology.spec raw (addresses p base entry) 4 topology)
        config rows mapping 1030 (queries p base entry) 4 (beforeFetchState entry) = true ∧
      NativeMteTagCheck.TagStatusRows entry (entry.choiceOcc.getD 1354 0) capacity := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨⟨⟨⟨⟨rawCheck, branch⟩, extras⟩, page, ret⟩, targets⟩, status⟩ := checked
  obtain ⟨topology, core, layout, current, present⟩ :=
    raw_of_check p image raw config rows mapping base entry rawCheck
  refine ⟨topology, core, BranchEntryMTE2.pins_of_check entry core.v1.features branch extras,
    ?_, layout, page, ret, List.all_eq_true.mp targets, current,
    TagStatusRows.of_check capacity entry status⟩
  exact ValuePlan.initial language _ _ _ _ _ _
    (Physical.Entry.snapshot_agrees (view p mapping entry) entry p.regions present)
    (Physical.Entry.snapshot_bounded (view p mapping entry) entry p.regions)

#print axioms fetch
#print axioms raw_of_check
#print axioms of_check
end TranslateSpan.SecpDefaultEntry
