import TranslateSpan.CheckedTopology
import TranslateSpan.CurrentMTE2
import TranslateSpan.StaticLayout
import TranslateSpan.EntryMatrix

open Sail ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ArmBridge.Draft
open ArmBridge.CruxGenGuarded NativeAccess ArmCertValue ArmCertPipe
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace TranslateSpan.SecpRawDeployment

structure PairAccess where
  index : Nat
  pin : Nat
  offset : Int
  write : Bool

structure Plan where
  code : List (Nat × Nat)
  accesses : List PairAccess
  regions : List (Region × Nat)
  buffers : List (Region × Nat)
  outputs : List (Region × Nat)
  normalize : Region → Region

def entryGPR (entry : NativeState) (pin : Nat) : BitVec 64 :=
  if h : pin < 31 then entry.regs.gpr[pin] else 0

def regionVA (entry : NativeState) (r : Region) (j : Nat) : BitVec 64 :=
  BitVec.addInt (entryGPR entry r.pin) (r.off + (j : Int))

def view (p : Plan) (mapping : BitVec 64 → Option Nat) (entry : NativeState) : Physical.BytePA :=
  fun r j => mapping (regionVA entry (p.normalize r) j)

def sites (p : Plan) (entry : NativeState) : List SelectedMap.Site :=
  p.accesses.map fun a => ⟨BitVec.addInt (entryGPR entry a.pin) a.offset, a.write⟩

def codeVAs (p : Plan) (base : BitVec 64) : List (BitVec 64) :=
  p.code.map fun c => MemReloc.imageAddress base c.1

def codeOffsets (p : Plan) : List Nat :=
  p.code.flatMap fun c => (List.range 4).map (c.1 + ·)

def selectedQueries (p : Plan) (base : BitVec 64) (entry : NativeState) : List AccessQuery :=
  SelectedRepresentatives.queries (QueryDescriptors.data false) (QueryDescriptors.data true)
    QueryDescriptors.fetch (sites p entry) (codeVAs p base)

def bufferQueries (p : Plan) (entry : NativeState) : List AccessQuery :=
  p.buffers.flatMap fun (r,n) => (List.range n).map fun j =>
    ⟨regionVA entry r j, ⟨QueryDescriptors.data (p.outputs.any (fun (g,_) => g == r)), true⟩, 1⟩

def queries (p : Plan) (base : BitVec 64) (entry : NativeState) : List AccessQuery :=
  selectedQueries p base entry ++ bufferQueries p entry

def addresses (p : Plan) (base : BitVec 64) (entry : NativeState) : List (BitVec 64) :=
  (queries p base entry).map (·.va)

def profile (entry : NativeState) : AccessProfile :=
  ⟨true, entry.regs.FeatureImpl[190]⟩

def offset (p : Plan) (k : Nat) : BitVec 64 :=
  BitVec.ofNat 64 ((p.code[k]?).getD (0, 0)).1

def consumer (p : Plan) (raw : CheckedTopology.Raw)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState) :
    ArmCert.Premises.TranslationAgreesV1.ConsumerMap :=
  SelectedMap.consumerMap (sites p entry) (codeVAs p base) mapping (rowsFootprint raw.imageRows).byte

def checkBuffers (p : Plan) (raw : CheckedTopology.Raw) (entry : NativeState) : Bool :=
  p.buffers.all fun (r, n) =>
    decide (0 ≤ (entryGPR entry r.pin).toNat + r.off ∧
      (entryGPR entry r.pin).toNat + r.off + (n : Int) ≤
        (2 ^ (min 55 raw.layout.inputBits) : Nat)) &&
    (regionVA entry r 0 == regionVA entry (p.normalize r) 0)

theorem bounds_of_check {p : Plan} {raw : CheckedTopology.Raw} {entry : NativeState}
    (checked : checkBuffers p raw entry = true) {r : Region} {n : Nat} (member : (r,n) ∈ p.buffers) :
    0 ≤ (entryGPR entry r.pin).toNat + r.off ∧
      (entryGPR entry r.pin).toNat + r.off + (n : Int) ≤
        (2 ^ (min 55 raw.layout.inputBits) : Nat) := by
  have row := List.all_eq_true.mp checked (r,n) member
  simp only [Bool.and_eq_true, decide_eq_true_eq] at row
  exact row.1

def checkLayout (p : Plan) (raw : CheckedTopology.Raw) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (entry : NativeState) : Bool :=
  let outputBytes := p.outputs.flatMap fun (r,n) => StaticLayout.outputPAs (view p mapping entry) r n
  checkBuffers p raw entry &&
    p.code.all (fun c => decide (base.toNat + c.1 + 4 ≤ 2 ^ (min 55 raw.layout.inputBits))) &&
    StaticLayout.checkInjective (view p mapping entry) (p.regions.map Prod.fst) &&
    StaticLayout.checkCodeAvoid (codeOffsets p) mapping base
      (fun pa => StaticLayout.footprintByte (rowsFootprint raw.imageRows) pa || outputBytes.contains pa) &&
    p.outputs.all (fun (r,n) => StaticLayout.checkOutput (view p mapping entry) r n (rowsFootprint raw.imageRows)) &&
    p.code.all (fun c => StaticLayout.checkCodeWord mapping base c.1)

def outputBytes (p : Plan) (mapping : BitVec 64 → Option Nat) (entry : NativeState) : List Nat :=
  p.outputs.flatMap fun (r,n) => StaticLayout.outputPAs (view p mapping entry) r n

structure LayoutFacts (p : Plan) (raw : CheckedTopology.Raw) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (entry : NativeState) : Prop where
  bounds : ∀ r n, (r,n) ∈ p.buffers →
    0 ≤ (entryGPR entry r.pin).toNat + r.off ∧
      (entryGPR entry r.pin).toNat + r.off + (n : Int) ≤
        (2 ^ (min 55 raw.layout.inputBits) : Nat)
  aliases : ∀ r n, (r,n) ∈ p.buffers → regionVA entry r 0 = regionVA entry (p.normalize r) 0
  codeRange : ∀ c ∈ p.code, base.toNat + c.1 + 4 ≤ 2 ^ (min 55 raw.layout.inputBits)
  injective : Physical.RegionsInjective (view p mapping entry) (p.regions.map Prod.fst)
  separated : ImageTableSeparated (· ∈ codeOffsets p) base mapping
    (fun pa => (rowsFootprint raw.imageRows).byte pa ∨ pa ∈ outputBytes p mapping entry)
  outputTable : ∀ r n, (r,n) ∈ p.outputs → ∀ j < n, ∀ pa,
    view p mapping entry r j = some pa → ¬ (rowsFootprint raw.imageRows).byte pa
  codeWords : ∀ c ∈ p.code,
    ImageWordContiguous mapping base c.1 ∧ MappedNotMMIO mapping (MemReloc.imageAddress base c.1)

theorem layout_of_check (p : Plan) (raw : CheckedTopology.Raw) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (entry : NativeState) (checked : checkLayout p raw mapping base entry = true) :
    LayoutFacts p raw mapping base entry := by
  simp only [checkLayout, Bool.and_eq_true] at checked
  obtain ⟨⟨⟨⟨⟨buffers, codeRange⟩, injective⟩, separated⟩, outputs⟩, words⟩ := checked
  refine ⟨fun r n member => bounds_of_check buffers member, ?_, ?_,
    StaticLayout.injective_of_check _ _ injective, ?_, ?_, ?_⟩
  · intro r n member
    have row := List.all_eq_true.mp buffers (r,n) member
    simp only [Bool.and_eq_true] at row
    exact beq_iff_eq.mp row.2
  · intro c member
    exact of_decide_eq_true (List.all_eq_true.mp codeRange c member)
  · apply StaticLayout.code_avoid_of_check (codeOffsets p) mapping base _ _ ?_ separated
    intro pa member
    rcases member with table | output
    · simp only [(StaticLayout.footprintByte_true _ _).mpr table, Bool.true_or]
    · have contains : (outputBytes p mapping entry).contains pa = true := List.contains_iff_mem.mpr output
      simp only [outputBytes] at contains
      simp only [contains, Bool.or_true]
  · intro r n member j bound pa mapped
    have row := List.all_eq_true.mp outputs (r,n) member
    have byte := List.all_eq_true.mp row j (List.mem_range.mpr bound)
    intro table
    simp only [mapped, (StaticLayout.footprintByte_true _ _).mpr table, Bool.not_true] at byte
    contradiction
  · intro c member
    exact StaticLayout.code_word_of_check mapping base c.1 (List.all_eq_true.mp words c member)

def check (p : Plan) (image : MemReloc.Image) (raw : CheckedTopology.Raw)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (entry : NativeState) : Bool :=
  if topology : CheckedTopology.check raw (addresses p base entry) 4 = true then
    let spec := CheckedTopology.spec raw (addresses p base entry) 4 topology
    CurrentMTE2.checkControls spec config rows (profile entry) (base + offset p 0) p.code.length entry &&
      MachineEntry.checkPlaced (codeOffsets p) image base mapping entry &&
      MachineEntry.checkPresent p.regions (view p mapping entry) entry &&
      CheckedEntry.checkQueries spec config rows mapping 1030 (queries p base entry) 4 (beforeFetchState entry) &&
      checkLayout p raw mapping base entry
  else false

theorem of_check (p : Plan) (image : MemReloc.Image) (raw : CheckedTopology.Raw)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (entry : NativeState)
    (checked : check p image raw config rows mapping base entry = true) :
    ∃ topology : CheckedTopology.check raw (addresses p base entry) 4 = true,
      CurrentMTE2.Core (CheckedTopology.spec raw (addresses p base entry) 4 topology)
        config rows mapping (consumer p raw mapping base entry) (· ∈ codeOffsets p) image
        base base (offset p) p.code.length (profile entry) 0 entry ∧
      LayoutFacts p raw mapping base entry ∧
      CheckedEntry.checkQueries (CheckedTopology.spec raw (addresses p base entry) 4 topology)
        config rows mapping 1030 (queries p base entry) 4 (beforeFetchState entry) = true ∧
      (∀ g j i k, memBL p.regions 0 g j = some (i,k) →
        (Physical.regionByte (view p mapping entry) entry g j).isSome = true) := by
  unfold check at checked
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
    exact ⟨topology, CurrentMTE2.core_of_checks spec config rows (profile entry)
      mapping (consumer p raw mapping base entry) (codeOffsets p) image base (offset p)
      p.code.length entry controls placed closed, layout_of_check p raw mapping base entry layout, current,
      MachineEntry.present_of_check p.regions (view p mapping entry) entry present⟩
  · contradiction

#print axioms bounds_of_check
#print axioms layout_of_check
#print axioms of_check
end TranslateSpan.SecpRawDeployment
