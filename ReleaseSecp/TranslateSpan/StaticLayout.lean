-- Finite checks on the declared virtual-to-physical map and physical footprints.
import PipeSecpSubPlan.CurrentRun
import PipeSecpSubPlan.CurrentEntry
open Sail ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ArmBridge.Draft
open ArmCertValue
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.StaticLayout

def footprintByte (f : Footprint) (pa : Nat) : Bool :=
  f.slots.any fun slot => decide (slot ≤ pa ∧ pa < slot + f.width)

theorem footprintByte_true (f : Footprint) (pa : Nat) :
    footprintByte f pa = true ↔ f.byte pa := by
  simp only [footprintByte, List.any_eq_true, decide_eq_true_eq, Footprint.byte]

def checkCodeAvoid (offsets : List Nat) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (bad : Nat → Bool) : Bool :=
  offsets.all fun o =>
    match mapping (MemReloc.imageAddress base o) with
    | none => false
    | some pa => !(bad pa)

theorem code_avoid_of_check (offsets : List Nat) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (bad : Nat → Bool) (f : Nat → Prop)
    (sound : ∀ pa, f pa → bad pa = true)
    (checked : checkCodeAvoid offsets mapping base bad = true) :
    ImageTableSeparated (fun o => o ∈ offsets) base mapping f := by
  intro o pa member mapped hf
  have h := List.all_eq_true.mp checked o member
  simp [mapped, sound pa hf] at h

def checkCodeWord (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (o : Nat) : Bool :=
  SelectedLoadFacts.checkRAM mapping (MemReloc.imageAddress base o) &&
    match mapping (MemReloc.imageAddress base o) with
    | none => false
    | some pa => (List.range 4).all fun i =>
        mapping (MemReloc.imageAddress base (o + i)) == some (pa + i)

theorem code_word_of_check (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (o : Nat)
    (checked : checkCodeWord mapping base o = true) :
    ImageWordContiguous mapping base o ∧ MappedNotMMIO mapping (MemReloc.imageAddress base o) := by
  simp only [checkCodeWord, Bool.and_eq_true] at checked
  obtain ⟨pa,mapped,notMMIO⟩ := SelectedLoadFacts.ram_of_check _ _ checked.1
  constructor
  · intro i hi a ha
    have all : (List.range 4).all (fun j =>
      mapping (MemReloc.imageAddress base (o+j)) == some (a+j)) = true := by
      simpa only [ha] using checked.2
    exact beq_iff_eq.mp (List.all_eq_true.mp all i (List.mem_range.mpr hi))
  · intro p hp
    have eq : p = pa := BitVec.eq_of_toNat_eq (Option.some.inj (hp.symm.trans mapped))
    rwa [eq]

/-- Check the exact finite tracked-byte relation for the chosen canonical layout. -/
def checkInjective (view : Physical.BytePA) (regions : List Region) : Bool :=
  (Physical.trackedBytes regions).all fun a =>
    (Physical.trackedBytes regions).all fun b =>
      decide (a = b) ||
        match view a.1 a.2, view b.1 b.2 with
        | some pa, some pb => pa != pb
        | _, _ => true

theorem injective_of_check (view : Physical.BytePA) (regions : List Region)
    (checked : checkInjective view regions = true) : Physical.RegionsInjective view regions := by
  intro a ha b hb ne pa hpa hpb
  have h := List.all_eq_true.mp (List.all_eq_true.mp checked a ha) b hb
  simp [ne,hpa,hpb] at h

def outputPAs (view : Physical.BytePA) (r : Region) (bytes : Nat) : List Nat :=
  (List.range bytes).filterMap (view r)

def checkOutput (view : Physical.BytePA) (r : Region) (bytes : Nat) (f : Footprint) : Bool :=
  (List.range bytes).all fun j =>
    match view r j with
    | none => false
    | some pa => !(footprintByte f pa)

theorem output_of_check {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (view : Physical.BytePA) (r : Region) (bytes word : Nat) (fits : 8 * word + 16 ≤ bytes)
    (checked : checkOutput view r bytes (rowsFootprint spec.imageRows) = true) :
    SelectedStoreFacts.OutputSafe spec view r word (fun pa => pa ∈ outputPAs view r bytes) := by
  intro i hi pa mapped
  have member := List.mem_range.mpr (show 8 * word + i < bytes by omega)
  have each := List.all_eq_true.mp checked _ member
  refine ⟨?_,List.mem_filterMap.mpr ⟨_,member,mapped⟩⟩
  intro hf
  simp [mapped,(footprintByte_true _ _).mpr hf] at each

#print axioms footprintByte
#print axioms footprintByte_true
#print axioms checkCodeAvoid
#print axioms code_avoid_of_check
#print axioms checkCodeWord
#print axioms code_word_of_check
#print axioms checkInjective
#print axioms injective_of_check
#print axioms outputPAs
#print axioms checkOutput
#print axioms output_of_check
end TranslateSpan.StaticLayout
