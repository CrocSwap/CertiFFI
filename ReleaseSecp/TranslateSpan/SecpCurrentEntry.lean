import TranslateSpan.SecpRawDeployment
import TranslateSpan.CurrentClass
import TranslateSpan.BranchEntryMTE2
import ArmCertValue.EntrySnapshot
import ArmCertPipe.GPrefix
import TranslateSpan.FetchCore

open Sail ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ArmBridge.Draft
open ArmBridge.CruxGenGuarded ArmCertValue ArmCertPipe NativeAccess
open ArmBridge.CruxGenGuarded.ChainInv
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace TranslateSpan.SecpCurrentEntry
open SecpRawDeployment

def inputs (p : Plan) (mapping : BitVec 64 → Option Nat) (entry : NativeState) : List (BitVec 64) :=
  mkInputsL entry p.regions (Physical.Entry.snapshot (view p mapping entry) entry p.regions)

theorem inputs_length (p : Plan) (mapping : BitVec 64 → Option Nat) (entry : NativeState) :
    (inputs p mapping entry).length = totalL p.regions + 36 :=
  Physical.Entry.snapshot_inputs_length (view p mapping entry) entry p.regions

theorem inputs_gpr (p : Plan) (mapping : BitVec 64 → Option Nat) (entry : NativeState)
    (pin : Nat) (valid : pin < 31) :
    (inputs p mapping entry).getD (totalL p.regions + pin) 0 = entryGPR entry pin := by
  unfold inputs
  rw [mkInputsL, mkInputsG_getD _ _ _ _ (by omega)]
  simp only [inputValG, ite_eq_right (show ¬ totalL p.regions + pin < totalL p.regions by omega),
    dite_eq_left (show totalL p.regions + pin < totalL p.regions + 31 by omega),
    Nat.add_sub_cancel_left, entryGPR, dite_eq_left valid]
  rfl

theorem initial_f (p : Plan) (mapping : BitVec 64 → Option Nat) (entry : NativeState)
    (regions : List Region) (plan : List ArmCertValue.F.Step)
    (present : ∀ g j i k, memBL p.regions 0 g j = some (i,k) →
      (Physical.regionByte (view p mapping entry) entry g j).isSome = true) :
    ArmCertPipe.F.AgreesAt (view p mapping entry) regions (σ0L p.regions)
      (inputs p mapping entry) plan 0 entry :=
  ArmCertPipe.F.agreesAt_zero
    (Physical.Entry.snapshot_agrees (view p mapping entry) entry p.regions present)
    (Physical.Entry.snapshot_bounded (view p mapping entry) entry p.regions)

theorem initial_g (p : Plan) (mapping : BitVec 64 → Option Nat) (entry : NativeState)
    (regions : List Region) (plan : List ArmCertValue.G.Step)
    (present : ∀ g j i k, memBL p.regions 0 g j = some (i,k) →
      (Physical.regionByte (view p mapping entry) entry g j).isSome = true) :
    ArmCertPipe.G.AgreesAt (view p mapping entry) regions (σ0L p.regions)
      (inputs p mapping entry) plan 0 entry :=
  ArmCertPipe.G.agreesAt_zero
    (Physical.Entry.snapshot_agrees (view p mapping entry) entry p.regions present)
    (Physical.Entry.snapshot_bounded (view p mapping entry) entry p.regions)

theorem regionVA_add (entry : NativeState) (r : Region) (j i : Nat) :
    PageSplit.byteVA (regionVA entry r j) i = regionVA entry r (j + i) := by
  simp only [PageSplit.byteVA, regionVA, BitVec.addInt, Int.natCast_add]
  rw [← Int.add_assoc, BitVec.ofInt_add (r.off + (j : Int)) (i : Int),
    BitVec.ofInt_natCast, BitVec.add_assoc]

theorem buffer_current {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (p : Plan)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState)
    (checked : CheckedEntry.checkQueries spec config rows mapping 1030 (queries p base entry)
      4 (beforeFetchState entry) = true)
    (r : Region) (n : Nat) (member : (r,n) ∈ p.buffers) (j : Nat) (bound : j < n) :
    PageSplit.CurrentAt spec config rows mapping (beforeFetchState entry) (regionVA entry r j) := by
  let q : AccessQuery := ⟨regionVA entry r j,
    ⟨QueryDescriptors.data (p.outputs.any (fun (g,_) => g == r)), true⟩, 1⟩
  have queryMember : q ∈ queries p base entry :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨(r,n), member,
      List.mem_map.mpr ⟨j, List.mem_range.mpr bound, rfl⟩⟩)
  obtain ⟨data, current⟩ := CheckedEntry.member_current checked q queryMember
  exact ⟨q, data, rfl, current⟩

theorem span {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (p : Plan)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState)
    (current : CurrentS1At spec config rows (beforeFetchState entry))
    (checked : CheckedEntry.checkQueries spec config rows mapping 1030 (queries p base entry)
      4 (beforeFetchState entry) = true)
    (r : Region) (n word : Nat) (member : (r,n) ∈ p.buffers)
    (fixed : p.normalize r = r) (fits : 8 * word + 16 ≤ n) :
    SelectedBinding.At (view p mapping entry) r word mapping (regionVA entry r (8 * word)) := by
  apply SelectedBinding.at_entry current.images.topology (view p mapping entry) r word _
  · intro j bound
    rw [regionVA_add]
    exact buffer_current spec config rows p mapping base entry checked r n member _ (by omega)
  · intro j bound
    simp only [view, fixed, regionVA_add]

def fetch {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (p : Plan) (raw : CheckedTopology.Raw)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState)
    (table : spec.imageRows = raw.imageRows) (layout : LayoutFacts p raw mapping base entry)
    (image : MemReloc.Image)
    (imageWords : ∀ c ∈ p.code, ∀ i < 4, image (c.1 + i) =
      some ((BitVec.ofNat 32 c.2).extractLsb' (8 * i) 8))
    (k : Nat) (x : NativeState)
    (inv : CurrentMTE2.Core spec config rows mapping (consumer p raw mapping base entry)
      (· ∈ codeOffsets p) image base base (offset p) p.code.length (profile entry) k x)
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

theorem code_table (p : Plan) (raw : CheckedTopology.Raw) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (entry : NativeState) (layout : LayoutFacts p raw mapping base entry) :
    ImageTableSeparated (· ∈ codeOffsets p) base mapping (rowsFootprint raw.imageRows).byte := by
  intro o pa inside mapped member
  exact layout.separated o pa inside mapped (Or.inl member)

theorem code_output (p : Plan) (raw : CheckedTopology.Raw) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (entry : NativeState) (layout : LayoutFacts p raw mapping base entry) :
    ImageTableSeparated (· ∈ codeOffsets p) base mapping (· ∈ outputBytes p mapping entry) := by
  intro o pa inside mapped member
  exact layout.separated o pa inside mapped (Or.inr member)

theorem table_output (p : Plan) (raw : CheckedTopology.Raw) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (entry : NativeState) (layout : LayoutFacts p raw mapping base entry) :
    Separated (rowsFootprint raw.imageRows).byte (· ∈ outputBytes p mapping entry) := by
  intro pa table output
  obtain ⟨⟨r,n⟩, member, inPair⟩ := List.mem_flatMap.mp output
  obtain ⟨j, bound, mapped⟩ := List.mem_filterMap.mp inPair
  exact layout.outputTable r n member j (List.mem_range.mp bound) pa mapped table

theorem output_safe {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (p : Plan) (raw : CheckedTopology.Raw) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (entry : NativeState) (table : spec.imageRows = raw.imageRows)
    (layout : LayoutFacts p raw mapping base entry)
    (r : Region) (n word : Nat) (member : (r,n) ∈ p.outputs) (fits : 8 * word + 16 ≤ n) :
    SelectedStoreFacts.OutputSafe spec (view p mapping entry) r word (· ∈ outputBytes p mapping entry) := by
  intro i bound pa mapped
  have index : 8 * word + i < n := by omega
  constructor
  · rw [table]
    exact layout.outputTable r n member _ index pa mapped
  · exact List.mem_flatMap.mpr ⟨(r,n), member,
      List.mem_filterMap.mpr ⟨8 * word + i, List.mem_range.mpr index, mapped⟩⟩

def check (p : Plan) (image : MemReloc.Image) (raw : CheckedTopology.Raw)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (entry : NativeState) : Bool :=
  SecpRawDeployment.check p image raw config rows mapping base entry &&
    BranchEntryMTE2.check entry && EntryControls.checkBranchExtras entry &&
    decide (base.toNat % 4096 = 0 ∧ (entryGPR entry 30).toNat < 2 ^ 55) &&
    (sites p entry).all (fun site => SelectedLoadFacts.checkTargets mapping site.address)

theorem of_check_f (p : Plan) (image : MemReloc.Image) (raw : CheckedTopology.Raw)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (entry : NativeState) (regions : List Region) (plan : List ArmCertValue.F.Step)
    (checked : check p image raw config rows mapping base entry = true) :
    ∃ topology : CheckedTopology.check raw (addresses p base entry) 4 = true,
      CurrentMTE2.Inv (CheckedTopology.spec raw (addresses p base entry) 4 topology)
        config rows mapping (consumer p raw mapping base entry) (· ∈ codeOffsets p) image
        base base (offset p) p.code.length (profile entry) (view p mapping entry)
        regions (σ0L p.regions) (inputs p mapping entry) plan 0 entry ∧
      LayoutFacts p raw mapping base entry ∧
      base.toNat % 4096 = 0 ∧ (entryGPR entry 30).toNat < 2 ^ 55 ∧
      (∀ site ∈ sites p entry, SelectedLoadFacts.checkTargets mapping site.address = true) ∧
      CheckedEntry.checkQueries (CheckedTopology.spec raw (addresses p base entry) 4 topology)
        config rows mapping 1030 (queries p base entry) 4 (beforeFetchState entry) = true := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨⟨⟨⟨rawCheck, branch⟩, extras⟩, page, ret⟩, targets⟩ := checked
  obtain ⟨topology, core, layout, current, present⟩ :=
    SecpRawDeployment.of_check p image raw config rows mapping base entry rawCheck
  exact ⟨topology, ⟨core, BranchEntryMTE2.pins_of_check entry core.v1.features branch extras,
    initial_f p mapping entry regions plan present⟩, layout, page, ret,
    List.all_eq_true.mp targets, current⟩

#print axioms inputs_length
#print axioms inputs_gpr
#print axioms initial_f
#print axioms initial_g
#print axioms regionVA_add
#print axioms buffer_current
#print axioms span
#print axioms fetch
#print axioms code_table
#print axioms code_output
#print axioms table_output
#print axioms output_safe
#print axioms of_check_f
end TranslateSpan.SecpCurrentEntry
