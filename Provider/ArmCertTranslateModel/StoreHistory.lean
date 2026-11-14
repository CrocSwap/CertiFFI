import ArmCertTranslateModel.AttributeBinding
import ArmCertTranslateModel.FlagValueFrame

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

/-- One raw source descriptor update. Roles belong to operations; another use
    of this same physical slot may have a different role. -/
structure TableUpdate where
  slot : Nat
  role : DescriptorRole
  before : BitVec 64
  after : BitVec 64

/-- Concrete memory effect to be DERIVED by the native source walk. The words
    are raw source descriptors; memory stores their actual endian encodings.
    No source-success, event-history or invariant-preservation field occurs. -/
structure StoreStep (params : S1TTWParams) (footprint : Footprint)
    (operation : TableUpdate) (before after : Mem) : Prop where
  covered : operation.slot ∈ footprint.slots
  aligned : operation.slot % 8 = 0
  present : S1ByteMemory.DescAt before operation.slot (S2Endian.encode params.ee operation.before)
  allowed : AllowedUpdate params operation.role operation.before operation.after
  stored : after = S1ByteMemory.store before operation.slot (S2Endian.encode params.ee operation.after)

/-- Ordered stores only. Reads and oracle/bookkeeping gaps may be framed by
    the source caller; their actual events must be retained separately. -/
inductive StoreHistory (params : S1TTWParams) (footprint : Footprint) :
    Mem → List TableUpdate → Mem → Prop
  | nil (memory : Mem) : StoreHistory params footprint memory [] memory
  | cons {first middle last : Mem} {operation : TableUpdate} {rest : List TableUpdate}
      (step : StoreStep params footprint operation first middle)
      (tail : StoreHistory params footprint middle rest last) :
      StoreHistory params footprint first (operation :: rest) last

theorem StoreHistory.append (first : StoreHistory params footprint a left b)
    (second : StoreHistory params footprint b right c) :
    StoreHistory params footprint a (left ++ right) c := by
  induction first with
  | nil => exact second
  | cons step tail ih => exact .cons step (ih second)

theorem StoreStep.frame (step : StoreStep params footprint operation before after)
    (width : footprint.width = 8) :
    WritesOnly footprint.byte (fun a => before[a]?) (fun a => after[a]?) := by
  intro address outside
  rw [step.stored]
  apply S1ByteMemory.lookup_outside
  by_cases low : address < operation.slot
  · exact Or.inl low
  · right
    have notInside : ¬ address < operation.slot + 8 := by
      intro high
      exact outside ⟨operation.slot, step.covered, by omega, by simpa only [width] using high⟩
    omega

theorem StoreHistory.frame (history : StoreHistory params footprint before operations after)
    (width : footprint.width = 8) :
    WritesOnly footprint.byte (fun a => before[a]?) (fun a => after[a]?) := by
  induction history with
  | nil => exact .refl _ _
  | cons step tail ih => exact (step.frame width).trans ih

/-- The image currently uses LE, derived at the actual getter from E3. This
    lemma exposes that requirement rather than treating a BE store as LE. -/
theorem StoreStep.le_present (step : StoreStep params footprint operation before after)
    (endian : params.ee = 0#1) : S1ByteMemory.DescAt before operation.slot operation.before := by
  have zero : (0#1 : BitVec 1) ≠ 1#1 := by decide
  simpa only [endian, S2Endian.encode, zero, ↓reduceIte] using step.present

theorem StoreStep.le_stored (step : StoreStep params footprint operation before after)
    (endian : params.ee = 0#1) : after = S1ByteMemory.store before operation.slot operation.after := by
  have zero : (0#1 : BitVec 1) ≠ 1#1 := by decide
  simpa only [endian, S2Endian.encode, zero, ↓reduceIte] using step.stored

theorem StoreHistory.preserves_image
    (history : StoreHistory params footprint before operations after)
    (endian : params.ee = 0#1) (aligned : ImageAligned observe)
    (image : ImageRealizes observe (params.pie == 1#1) (params.ha == 1#1)
      (params.hd == 1#1) before) :
    ImageRealizes observe (params.pie == 1#1) (params.ha == 1#1) (params.hd == 1#1) after := by
  induction history with
  | nil => exact image
  | cons step tail ih =>
    apply ih
    rw [step.le_stored endian]
    exact allowed_image_store params _ _ _ _ _ observe step.allowed image aligned step.aligned
      (step.le_present endian)

theorem StoreHistory.preserves_attributes
    (history : StoreHistory params footprint before operations after)
    (endian : params.ee = 0#1) (aligned : ImageAligned observe)
    (attributes : AttributeImage observe config before) : AttributeImage observe config after := by
  induction history with
  | nil => exact attributes
  | cons step tail ih =>
    apply ih
    rw [step.le_stored endian]
    exact attributes.hardware_store params _ _ _ _ step.allowed step.aligned aligned
      (step.le_present endian)

theorem StoreHistory.preserves_normal
    (history : StoreHistory params footprint before operations after)
    (endian : params.ee = 0#1) (aligned : ImageAligned observe)
    (normal : NormalAttributeImage observe config before) : NormalAttributeImage observe config after := by
  induction history with
  | nil => exact normal
  | cons step tail ih =>
    apply ih
    rw [step.le_stored endian]
    exact normal.hardware_store params _ _ _ _ step.allowed step.aligned aligned
      (step.le_present endian)

def historyFlagBytes (operations : List TableUpdate) (address : Nat) : Prop :=
  ∃ operation ∈ operations, FlagValueByte operation.slot address

/-- Potential value changes follow the actual ordered slots. This does NOT
    shrink any eight-byte native TTW write event or identify paired histories. -/
theorem StoreHistory.flag_value_frame
    (history : StoreHistory params footprint before operations after)
    (endian : params.ee = 0#1) :
    WritesOnly (historyFlagBytes operations) (fun a => before[a]?) (fun a => after[a]?) := by
  induction history with
  | nil => exact .refl _ _
  | @cons first middle last operation rest step tail ih =>
    intro address outside
    have firstFrame := allowed_store_value_frame params operation.role operation.before operation.after
      step.allowed first operation.slot (step.le_present endian)
    rw [← step.le_stored endian] at firstFrame
    apply (ih address ?_).trans (firstFrame address ?_)
    · rintro ⟨op, member, flag⟩
      exact outside ⟨op, List.mem_cons_of_mem _ member, flag⟩
    · intro flag
      exact outside ⟨operation, List.mem_cons_self, flag⟩

#print axioms StoreHistory.append
#print axioms StoreHistory.frame
#print axioms StoreHistory.preserves_image
#print axioms StoreHistory.preserves_attributes
#print axioms StoreHistory.preserves_normal
#print axioms StoreHistory.flag_value_frame
end ArmCert.Translate.Model
