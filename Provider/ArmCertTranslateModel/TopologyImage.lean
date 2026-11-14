import ArmCertTranslateModel.CheckImage
import ArmCertTranslateModel.StructuralBridge

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

/-- Preserve the whole actual request and the size omitted by the older Request
    carrier. This is exactly the consumer permitted-access query. -/
structure AccessQuery where
  va : BitVec 64
  request : S1LogicalReference.Request
  size : Int

/-- Declared query domain. Membership of each actual request is a producer
    proof obligation, not a future-membership answer in execution entry. -/
abbrev QueryDomain := AccessQuery → Prop

structure LogicalRow where
  logical : Nat
  physical : FullAddress
  view : S1DescriptorPIE.View 64

def logicalObserve (rows : List LogicalRow) : S1LogicalReference.Observation :=
  fun logical physical view =>
    ∃ row ∈ rows, logical = row.logical ∧ physical = row.physical ∧ view = row.view

/-- Finite topology/image component ONLY. Actual current-register/root binding
    and effective permission/attribute access admission are separate components
    awaiting memory's typed source API. This record contains no source-call,
    future-preservation or arbitrary admission callback field. -/
structure TopologyImageSpec (domain : QueryDomain) where
  params : S1TTWParams
  physicalConfig : PhysicalConfig
  controls : S1LogicalReference.Controls
  layout : S1LogicalReference.Layout
  logicalRows : List LogicalRow
  imageRows : List ImageRow
  available : S1LogicalReference.Available (logicalObserve logicalRows)
    (fun p => S2TableRAM.OrdinaryRAM p.address)
  identity : ∀ logical physical view, logicalObserve logicalRows logical physical view →
    logical = physical.address.toNat ∧ physical.paspace = .PAS_NonSecure
  represented : ∀ logical physical view, logicalObserve logicalRows logical physical view →
    ∃ leaf, rowsObserve imageRows physical.address.toNat leaf view
  aligned : ImageAligned (rowsObserve imageRows)
  /-- Existing Path checks child ranges; the initial root slot needs its own
      current structural address-size check. No future call result is used. -/
  rootBound : ∀ q : AccessQuery, domain q →
    S1LogicalReference.entryAddress layout.root q.va layout.start
      (S1LogicalReference.rootBits layout.start layout.inputBits) <
      2 ^ (effectiveBits physicalConfig).toNat
  paths : ∀ q : AccessQuery, domain q →
    ∃ level logical physical view,
      S1LogicalReference.Path (logicalObserve logicalRows) (effectiveBits physicalConfig).toNat q.va
        layout.start (S1LogicalReference.rootBits layout.start layout.inputBits) layout.root
        (.leaf level logical physical view) ∧
      rowsObserve imageRows physical.address.toNat true view

/-- Current bytes realize the static topology's stable views and role readiness.
    Inactive raw initialization witnesses in imageRows need not stay equal. -/
def TopologyImageAt {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (state : State) : Prop :=
  ImageRealizes (rowsObserve spec.imageRows) (spec.params.pie == 1#1)
    (spec.params.ha == 1#1) (spec.params.hd == 1#1) state.mem

theorem topology_covers {domain : QueryDomain}
    (spec : TopologyImageSpec domain) :
    S1LogicalReference.Covers (logicalObserve spec.logicalRows) (rowsFootprint spec.imageRows).byte := by
  intro logical physical view ho i hi
  obtain ⟨leaf, huse⟩ := spec.represented logical physical view ho
  have hs := rows_covered spec.imageRows _ leaf view huse
  exact (rowsFootprint spec.imageRows).covers _ hs ⟨i, hi⟩

theorem topology_realizes {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (state : State) (h : TopologyImageAt spec state) :
    S1LogicalReference.Realizes (logicalObserve spec.logicalRows) false
      (spec.params.pie == 1#1) (spec.params.ha == 1#1) (spec.params.hd == 1#1)
      (fun a => state.mem[a]?) := by
  intro logical physical view ho
  obtain ⟨leaf, huse⟩ := spec.represented logical physical view ho
  obtain ⟨d, hb, hv, _⟩ := h _ leaf view huse
  refine ⟨d, ?_, hv⟩
  intro i hi
  simpa only [S1LogicalReference.byte, Bool.false_eq_true, ↓reduceIte] using hb i hi

/-- Static paths remain fixed while the endpoint's CURRENT raw bytes/readiness
    are recovered from the preserved image, including on clean updated pages. -/
theorem topology_leaf_inputs {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (state : State) (h : TopologyImageAt spec state)
    (query : AccessQuery) (hq : domain query) :
    ∃ level logical physical view d,
      S1LogicalReference.Path (logicalObserve spec.logicalRows) (effectiveBits spec.physicalConfig).toNat query.va
        spec.layout.start (S1LogicalReference.rootBits spec.layout.start spec.layout.inputBits) spec.layout.root
        (.leaf level logical physical view) ∧
      S1LogicalReference.BytesAt false (fun a => state.mem[a]?) physical d ∧
      S1DescriptorPIE.view (spec.params.pie == 1#1) (spec.params.ha == 1#1) (spec.params.hd == 1#1) d = view ∧
      ArmCertWalk.AFReady spec.params .leaf d := by
  obtain ⟨level, logical, physical, view, hp, hleaf⟩ := spec.paths query hq
  obtain ⟨d, hb, hv, hr⟩ := h _ true view hleaf
  refine ⟨level, logical, physical, view, d, hp, ?_, hv, ?_⟩
  · intro i hi
    simpa only [S1LogicalReference.byte, Bool.false_eq_true, ↓reduceIte] using hb i hi
  · exact (afReady_iff spec.params .leaf d).mpr hr

theorem topology_check_initial {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (state : State)
    (h : checkImage spec.imageRows (spec.params.pie == 1#1)
      (spec.params.ha == 1#1) (spec.params.hd == 1#1) state.mem = true) :
    TopologyImageAt spec state := checkImage_realizes _ _ _ _ _ h

theorem topology_program_write {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (s t : State) (h : TopologyImageAt spec s)
    (writes : Nat → Prop) (hf : WritesOnly writes (fun a => s.mem[a]?) (fun a => t.mem[a]?))
    (hs : Separated (rowsFootprint spec.imageRows).byte writes) : TopologyImageAt spec t := by
  exact h.program_write (rowsFootprint spec.imageRows) rfl (rows_covered spec.imageRows) hf hs

/-- Actual authorized word changes preserve the topology/image component; the
    native walk supplies the actual write equation separately. -/
theorem topology_allowed_store {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (s t : State) (h : TopologyImageAt spec s)
    (role : DescriptorRole) (slot : Nat) (before after : BitVec 64)
    (hu : AllowedUpdate spec.params role before after) (hal : slot % 8 = 0)
    (hb : S1ByteMemory.DescAt s.mem slot before)
    (hm : t.mem = S1ByteMemory.store s.mem slot after) : TopologyImageAt spec t := by
  rw [TopologyImageAt, hm]
  exact allowed_image_store spec.params role before after s.mem slot (rowsObserve spec.imageRows)
    hu h spec.aligned hal hb

/-- A new actual getter result need only match the active image controls.
    Inactive/undefined fields may vary with its real oracle history. -/
theorem topology_image_reparam {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (state : State) (actual : S1TTWParams)
    (hpie : actual.pie = spec.params.pie) (hha : actual.ha = spec.params.ha)
    (hhd : actual.hd = spec.params.hd) :
    TopologyImageAt {spec with params := actual} state ↔ TopologyImageAt spec state := by
  simp only [TopologyImageAt, hpie, hha, hhd]

#print axioms topology_realizes
#print axioms topology_leaf_inputs
#print axioms topology_check_initial
#print axioms topology_program_write
#print axioms topology_allowed_store
end ArmCert.Translate.Model
