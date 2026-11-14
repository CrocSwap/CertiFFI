import ArmCertWalk.AttributeFacts
import ArmCertTranslateModel.AttributePreservation

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

/-- The selected byte is Normal exactly when its high nibble is nonzero.
    Reserved encodings are checked independently by AttributeImage. -/
def NormalAttributeImage (observe : RoleObservation) (config : AttributeConfig)
    (mem : Mem) : Prop :=
  ∀ slot view, observe slot true view → ∀ d, S1ByteMemory.DescAt mem slot d →
    attributeHigh (selectedAttribute config d) ≠ 0#4

def checkNormalAttributeImage (rows : List ImageRow) (config : AttributeConfig) : Bool :=
  rows.all (fun row => !row.leaf || decide (attributeHigh (selectedAttribute config row.raw) ≠ 0#4))

theorem check_normal_attribute_image_sound (rows : List ImageRow) (config : AttributeConfig)
    (params : S1TTWParams) (mem : Mem)
    (hbytes : checkImage rows (params.pie == 1#1) (params.ha == 1#1) (params.hd == 1#1) mem = true)
    (hnormal : checkNormalAttributeImage rows config = true) :
    NormalAttributeImage (rowsObserve rows) config mem := by
  intro slot view ⟨row, hr, hs, hl, _⟩ d hd
  obtain ⟨hraw, _, _, _⟩ := row.check_sound _ _ _ _ ((List.all_eq_true.mp hbytes) row hr)
  have heq : d = row.raw := S1ByteMemory.descriptor_unique mem row.slot d row.raw
    (by simpa [hs] using hd) hraw
  rw [heq]
  have hleaf : row.leaf = true := hl.symm
  simpa only [hleaf, Bool.not_true, Bool.false_or, decide_eq_true_eq] using
    ((List.all_eq_true.mp hnormal) row hr)

theorem NormalAttributeImage.hardware_store (h : NormalAttributeImage observe config mem)
    (params : S1TTWParams) (role : DescriptorRole) (slot : Nat) (before after : BitVec 64)
    (hu : AllowedUpdate params role before after) (hAlign : slot % 8 = 0)
    (hSlots : ImageAligned observe) (hb : S1ByteMemory.DescAt mem slot before) :
    NormalAttributeImage observe config (S1ByteMemory.store mem slot after) := by
  intro b view ho d hd
  by_cases heq : slot = b
  · subst b
    have hnew : d = after := S1ByteMemory.descriptor_unique _ slot d after hd
      (S1ByteMemory.stored_descriptor _ _ _)
    rw [hnew, allowed_selected_attribute params role before after hu config]
    exact h slot view ho before hb
  · exact h b view ho d
      ((S1ByteMemory.other_descriptor_iff mem slot b after d hAlign (hSlots b true view ho) heq).mp hd)

theorem NormalAttributeImage.program_write (h : NormalAttributeImage observe config mem)
    (f : Footprint) (hw : f.width = 8) (hc : ImageCovers observe f)
    (hf : WritesOnly writes (fun a => mem[a]?) (fun a => mem'[a]?))
    (hs : Separated f.byte writes) : NormalAttributeImage observe config mem' := by
  intro slot view ho d hd
  apply h slot view ho d
  intro i hi
  have hi' : i < f.width := by simpa only [hw] using hi
  have heq := table_unchanged hf hs _ (f.covers slot (hc slot true view ho) ⟨i, hi'⟩)
  exact heq.symm.trans (hd i hi)

/-- Source meaning proves Normal; no oracle-independent equality of inactive
    cache fields or exclusion of SH=1 is needed. -/
theorem interpreted_normal (attr : BitVec 8) (sh : BitVec 2) (params : S1TTWParams)
    (attrs : MemoryAttributes) (h : AttributeInterprets attr sh params attrs)
    (hnormal : attributeHigh attr ≠ 0#4) : attrs.memtype = .MemType_Normal := by
  have hk := congrArg AttributeBody.kind h.1
  cases ht : attrs.memtype with
  | MemType_Device =>
    simp only [attributeProjection, ht, decodedAttributeBody, hnormal, ↓reduceIte] at hk
    split at hk
    · contradiction
    · split at hk
      · contradiction
      · split at hk <;> contradiction
  | MemType_Normal => rfl

/-- Current image bytes and pure byte checks derive actual selected decoding
    and Normal memory at the same source successor. All frames are conclusions.
    This is a leaf decoder bridge, not the native walk or access admission. -/
theorem image_selected_attribute_total {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (config : AttributeConfig) (state : State)
    (image : TopologyImageAt spec state)
    (valid : AttributeImage (rowsObserve spec.imageRows) config state.mem)
    (normal : NormalAttributeImage (rowsObserve spec.imageRows) config state.mem)
    (current : ActiveAttributesAt config spec.params state)
    (slot : Nat) (view : S1DescriptorPIE.View 64)
    (used : rowsObserve spec.imageRows slot true view) (sh : BitVec 2) :
    ∃ descriptor attrs next,
      S1ByteMemory.DescAt state.mem slot descriptor ∧
      S1DescriptorPIE.view (spec.params.pie == 1#1) (spec.params.ha == 1#1)
        (spec.params.hd == 1#1) descriptor = view ∧
      AFReady spec.params .leaf descriptor ∧
      (do
        let attr ← AArch64_MAIRAttr (S1MAIRKernel.index descriptor) spec.params.mair2 spec.params.mair
        S1DecodeMemAttrs attr sh true spec.params) state = .ok attrs next ∧
      AttributeInterprets (selectedAttribute config descriptor) sh spec.params attrs ∧
      attrs.memtype = .MemType_Normal ∧
      next.regs = state.regs ∧ next.mem = state.mem ∧ next.events = state.events ∧
      TopologyImageAt spec next ∧
      AttributeImage (rowsObserve spec.imageRows) config next.mem ∧
      NormalAttributeImage (rowsObserve spec.imageRows) config next.mem ∧
      ActiveAttributesAt config spec.params next := by
  obtain ⟨d, bytes, observed, ready⟩ := image slot true view used
  obtain ⟨attrs, next, call, meaning, regs, mem, events⟩ :=
    selected_attribute_total config spec.params state current d sh (valid slot view used d bytes)
  refine ⟨d, attrs, next, bytes, observed, (afReady_iff spec.params .leaf d).mpr ready,
    call, meaning, interpreted_normal _ _ _ _ meaning (normal slot view used d bytes),
    regs, mem, events, ?_, ?_, ?_, current.of_regs regs⟩
  · unfold TopologyImageAt
    rw [mem]
    exact image
  · rw [mem]; exact valid
  · rw [mem]; exact normal

#print axioms check_normal_attribute_image_sound
#print axioms NormalAttributeImage.hardware_store
#print axioms NormalAttributeImage.program_write
#print axioms interpreted_normal
#print axioms image_selected_attribute_total
end ArmCert.Translate.Model
