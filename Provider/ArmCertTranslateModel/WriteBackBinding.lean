import ArmCertTranslateModel.AttributeBinding
import ArmCertTranslateModel.StoreHistory

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

/-- Inspect the existing source-checked active attribute interpretation. This
    Boolean adds no second MAIR decoder and ignores no active cache policy. -/
def normalWriteBack : S1LogicalReference.AttributeKind → Bool
  | .device _ => false
  | .normal inner outer => (inner.attrs == MemAttr_WB) && (outer.attrs == MemAttr_WB)

def writeBackByte (attr : BitVec 8) : Bool :=
  normalWriteBack (decodedAttributeBody attr 0#1).kind

def WriteBackAttributeImage (observe : RoleObservation) (config : AttributeConfig)
    (mem : Mem) : Prop :=
  ∀ slot view, observe slot true view → ∀ d, S1ByteMemory.DescAt mem slot d →
    writeBackByte (selectedAttribute config d) = true

def checkWriteBackAttributeImage (rows : List ImageRow) (config : AttributeConfig) : Bool :=
  rows.all (fun row => !row.leaf || writeBackByte (selectedAttribute config row.raw))

theorem check_writeback_attribute_image_sound (rows : List ImageRow) (config : AttributeConfig)
    (params : S1TTWParams) (mem : Mem)
    (hbytes : checkImage rows (params.pie == 1#1) (params.ha == 1#1) (params.hd == 1#1) mem = true)
    (hwb : checkWriteBackAttributeImage rows config = true) :
    WriteBackAttributeImage (rowsObserve rows) config mem := by
  intro slot view ⟨row, hr, hs, hl, _⟩ d hd
  obtain ⟨hraw, _, _, _⟩ := row.check_sound _ _ _ _ ((List.all_eq_true.mp hbytes) row hr)
  have heq : d = row.raw := S1ByteMemory.descriptor_unique mem row.slot d row.raw
    (by simpa [hs] using hd) hraw
  rw [heq]
  have leaf : row.leaf = true := hl.symm
  simpa only [leaf, Bool.not_true, Bool.false_or] using ((List.all_eq_true.mp hwb) row hr)

theorem WriteBackAttributeImage.hardware_store (h : WriteBackAttributeImage observe config mem)
    (params : S1TTWParams) (role : DescriptorRole) (slot : Nat) (before after : BitVec 64)
    (hu : AllowedUpdate params role before after) (aligned : slot % 8 = 0)
    (slots : ImageAligned observe) (present : S1ByteMemory.DescAt mem slot before) :
    WriteBackAttributeImage observe config (S1ByteMemory.store mem slot after) := by
  intro b view used d bytes
  by_cases same : slot = b
  · subst b
    have new : d = after := S1ByteMemory.descriptor_unique _ slot d after bytes
      (S1ByteMemory.stored_descriptor _ _ _)
    rw [new, allowed_selected_attribute params role before after hu config]
    exact h slot view used before present
  · exact h b view used d
      ((S1ByteMemory.other_descriptor_iff mem slot b after d aligned (slots b true view used) same).mp bytes)

theorem WriteBackAttributeImage.program_write (h : WriteBackAttributeImage observe config mem)
    (footprint : Footprint) (width : footprint.width = 8) (covered : ImageCovers observe footprint)
    (frame : WritesOnly writes (fun a => mem[a]?) (fun a => mem'[a]?))
    (separated : Separated footprint.byte writes) : WriteBackAttributeImage observe config mem' := by
  intro slot view used d bytes
  apply h slot view used d
  intro i hi
  have bound : i < footprint.width := by simpa only [width] using hi
  have same := table_unchanged frame separated _ (footprint.covers slot (covered slot true view used) ⟨i, bound⟩)
  exact same.symm.trans (bytes i hi)

theorem WriteBackAttributeImage.normal (h : WriteBackAttributeImage observe config mem) :
    NormalAttributeImage observe config mem := by
  intro slot view used d bytes device
  have wb := h slot view used d bytes
  simp only [writeBackByte, decodedAttributeBody, device, ↓reduceIte, normalWriteBack] at wb
  contradiction

theorem StoreHistory.preserves_writeback
    (history : StoreHistory params footprint before operations after)
    (endian : params.ee = 0#1) (aligned : ImageAligned observe)
    (wb : WriteBackAttributeImage observe config before) : WriteBackAttributeImage observe config after := by
  induction history with
  | nil => exact wb
  | cons step tail ih =>
    apply ih
    rw [step.le_stored endian]
    exact wb.hardware_store params _ _ _ _ step.allowed step.aligned aligned (step.le_present endian)

theorem interpreted_writeback (attr : BitVec 8) (sh : BitVec 2) (params : S1TTWParams)
    (attrs : MemoryAttributes) (meaning : AttributeInterprets attr sh params attrs)
    (wb : writeBackByte attr = true) :
    attrs.memtype = .MemType_Normal ∧ attrs.inner.attrs = MemAttr_WB ∧ attrs.outer.attrs = MemAttr_WB := by
  have kind := congrArg AttributeBody.kind meaning.1
  have actual : normalWriteBack (attributeProjection attrs).kind = true := by
    rw [kind]
    exact wb
  cases memoryType : attrs.memtype with
  | MemType_Device => simp [attributeProjection, memoryType, normalWriteBack] at actual
  | MemType_Normal =>
    simp only [attributeProjection, memoryType, normalWriteBack, cacheProjection,
      Bool.and_eq_true, beq_iff_eq] at actual
    exact ⟨rfl, actual⟩

/-- Strengthen the actual decoder result using the preserved finite WB check.
    This still concerns the leaf decoder, not full TranslateAddress. -/
theorem image_selected_writeback_total {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (config : AttributeConfig) (state : State)
    (image : TopologyImageAt spec state)
    (valid : AttributeImage (rowsObserve spec.imageRows) config state.mem)
    (wb : WriteBackAttributeImage (rowsObserve spec.imageRows) config state.mem)
    (current : ActiveAttributesAt config spec.params state)
    (slot : Nat) (view : S1DescriptorPIE.View 64)
    (used : rowsObserve spec.imageRows slot true view) (sh : BitVec 2) :
    ∃ descriptor attrs next,
      S1ByteMemory.DescAt state.mem slot descriptor ∧
      (do
        let attr ← AArch64_MAIRAttr (S1MAIRKernel.index descriptor) spec.params.mair2 spec.params.mair
        S1DecodeMemAttrs attr sh true spec.params) state = .ok attrs next ∧
      AttributeInterprets (selectedAttribute config descriptor) sh spec.params attrs ∧
      attrs.memtype = .MemType_Normal ∧ attrs.inner.attrs = MemAttr_WB ∧ attrs.outer.attrs = MemAttr_WB ∧
      next.regs = state.regs ∧ next.mem = state.mem ∧ next.events = state.events ∧
      TopologyImageAt spec next ∧ AttributeImage (rowsObserve spec.imageRows) config next.mem ∧
      WriteBackAttributeImage (rowsObserve spec.imageRows) config next.mem ∧
      ActiveAttributesAt config spec.params next := by
  obtain ⟨d, attrs, next, bytes, _, _, call, meaning, _, registers, memory, events,
    nextImage, nextValid, _, nextCurrent⟩ :=
    image_selected_attribute_total spec config state image valid wb.normal current slot view used sh
  obtain ⟨normal, inner, outer⟩ := interpreted_writeback _ _ _ _ meaning (wb slot view used d bytes)
  refine ⟨d, attrs, next, bytes, call, meaning, normal, inner, outer,
    registers, memory, events, nextImage, nextValid, ?_, nextCurrent⟩
  rw [memory]; exact wb

#print axioms check_writeback_attribute_image_sound
#print axioms WriteBackAttributeImage.hardware_store
#print axioms WriteBackAttributeImage.program_write
#print axioms StoreHistory.preserves_writeback
#print axioms interpreted_writeback
#print axioms image_selected_writeback_total
end ArmCert.Translate.Model
