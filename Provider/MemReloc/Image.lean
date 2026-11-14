import Init.Data.BitVec.Lemmas
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 150000

namespace MemReloc

abbrev Byte := BitVec 8
abbrev Word := BitVec 64
abbrev Image := Nat → Option Byte

/-- Normalized PT_LOAD metadata. Raw-format admission belongs to the checker. -/
structure LoadSegment where
  fileOffset : Nat
  imageOffset : Nat
  fileSize : Nat
  memorySize : Nat
  deriving Repr

/-- Explicit order is part of this normalized model, including overlapping loads. -/
def loadSegment (file previous : Image) (segment : LoadSegment) : Image := fun offset =>
  if segment.imageOffset ≤ offset ∧ offset < segment.imageOffset + segment.memorySize then
    if offset - segment.imageOffset < segment.fileSize then
      file (segment.fileOffset + (offset - segment.imageOffset))
    else some 0
  else previous offset

def loadSegments (file : Image) (segments : List LoadSegment) : Image :=
  segments.foldl (loadSegment file) (fun _ => none)

/-- An explicit normalized addend; no implicit ELF addend decoding is claimed. -/
structure RelativePatch where
  imageOffset : Nat
  addend : Word
  deriving Repr

def wordByte (word : Word) (index : Nat) : Byte := word.extractLsb' (8 * index) 8

def applyRelative (base : Word) (previous : Image) (patch : RelativePatch) : Image :=
  fun offset =>
    if patch.imageOffset ≤ offset ∧ offset < patch.imageOffset + 8 then
      some (wordByte (base + patch.addend) (offset - patch.imageOffset))
    else previous offset

def relocatedImage (file : Image) (segments : List LoadSegment)
    (patches : List RelativePatch) (base : Word) : Image :=
  patches.foldl (applyRelative base) (loadSegments file segments)

theorem loadSegment_file (file previous : Image) (segment : LoadSegment) (offset : Nat)
    (inside : segment.imageOffset ≤ offset ∧
      offset < segment.imageOffset + segment.memorySize)
    (fileByte : offset - segment.imageOffset < segment.fileSize) :
    loadSegment file previous segment offset =
      file (segment.fileOffset + (offset - segment.imageOffset)) := by
  simp [loadSegment, inside, fileByte]

theorem loadSegment_zero (file previous : Image) (segment : LoadSegment) (offset : Nat)
    (inside : segment.imageOffset ≤ offset ∧
      offset < segment.imageOffset + segment.memorySize)
    (tailByte : ¬ offset - segment.imageOffset < segment.fileSize) :
    loadSegment file previous segment offset = some 0 := by
  simp [loadSegment, inside, tailByte]

theorem loadSegment_frame (file previous : Image) (segment : LoadSegment) (offset : Nat)
    (outside : ¬ (segment.imageOffset ≤ offset ∧
      offset < segment.imageOffset + segment.memorySize)) :
    loadSegment file previous segment offset = previous offset := by
  simp [loadSegment, outside]

theorem applyRelative_byte (base : Word) (previous : Image) (patch : RelativePatch)
    (index : Nat) (bound : index < 8) :
    applyRelative base previous patch (patch.imageOffset + index) =
      some (wordByte (base + patch.addend) index) := by
  simp [applyRelative, show patch.imageOffset ≤ patch.imageOffset + index by omega,
    show patch.imageOffset + index < patch.imageOffset + 8 by omega]

theorem applyRelative_frame (base : Word) (previous : Image) (patch : RelativePatch)
    (offset : Nat) (outside : ¬ (patch.imageOffset ≤ offset ∧
      offset < patch.imageOffset + 8)) :
    applyRelative base previous patch offset = previous offset := by
  simp [applyRelative, outside]

/-- An ordered patch list leaves a byte unchanged exactly when every patch
    excludes it. No sorting or overlap normalization is hidden here. -/
theorem patches_frame (base : Word) (patches : List RelativePatch)
    (previous : Image) (offset : Nat)
    (outside : ∀ patch ∈ patches,
      ¬ (patch.imageOffset ≤ offset ∧ offset < patch.imageOffset + 8)) :
    patches.foldl (applyRelative base) previous offset = previous offset := by
  induction patches generalizing previous with
  | nil => rfl
  | cons patch patches ih =>
    simp only [List.foldl_cons]
    rw [ih (applyRelative base previous patch)
      (fun next hn => outside next (List.mem_cons_of_mem patch hn))]
    exact applyRelative_frame base previous patch offset (outside patch List.mem_cons_self)

/-- Appending operations preserves their declared order; later patches may
    replace earlier bytes. -/
theorem patches_append (base : Word) (first last : List RelativePatch)
    (previous : Image) :
    (first ++ last).foldl (applyRelative base) previous =
      last.foldl (applyRelative base) (first.foldl (applyRelative base) previous) := by
  exact List.foldl_append

def DisjointPatches (left right : RelativePatch) : Prop :=
  left.imageOffset + 8 ≤ right.imageOffset ∨ right.imageOffset + 8 ≤ left.imageOffset

/-- Distinct nonoverlapping writes commute. This does not infer disjointness
    from a raw ELF table or change the ordered definition of relocatedImage. -/
theorem applyRelative_commute (base : Word) (previous : Image)
    (left right : RelativePatch) (separate : DisjointPatches left right) :
    applyRelative base (applyRelative base previous left) right =
      applyRelative base (applyRelative base previous right) left := by
  funext offset
  by_cases hl : left.imageOffset ≤ offset ∧ offset < left.imageOffset + 8
  · have hr : ¬ (right.imageOffset ≤ offset ∧ offset < right.imageOffset + 8) := by
      rcases separate with h | h <;> omega
    simp [applyRelative, hl, hr]
  · by_cases hr : right.imageOffset ≤ offset ∧ offset < right.imageOffset + 8
    · simp [applyRelative, hl, hr]
    · simp [applyRelative, hl, hr]

/-- Every byte of an implicit-addend slot is unchanged by preceding patches
    whose eight-byte targets are disjoint. A loader binding must separately
    establish these intervals and stable relocation-table metadata. -/
theorem patches_frame_slot (base : Word) (patches : List RelativePatch)
    (previous : Image) (slot index : Nat) (bound : index < 8)
    (separate : ∀ patch ∈ patches,
      patch.imageOffset + 8 ≤ slot ∨ slot + 8 ≤ patch.imageOffset) :
    patches.foldl (applyRelative base) previous (slot + index) = previous (slot + index) := by
  apply patches_frame
  intro patch member inside
  rcases separate patch member with h | h <;> omega

theorem relocatedImage_unpatched (file : Image) (segments : List LoadSegment)
    (patches : List RelativePatch) (base : Word) (offset : Nat)
    (outside : ∀ patch ∈ patches,
      ¬ (patch.imageOffset ≤ offset ∧ offset < patch.imageOffset + 8)) :
    relocatedImage file segments patches base offset = loadSegments file segments offset := by
  exact patches_frame base patches (loadSegments file segments) offset outside

/-- A final patch provides its eight current image bytes even when earlier
    operations overlap it. This does not admit such overlap in an ELF checker. -/
theorem relocatedImage_last_patch (file : Image) (segments : List LoadSegment)
    (patches : List RelativePatch) (last : RelativePatch) (base : Word)
    (index : Nat) (bound : index < 8) :
    relocatedImage file segments (patches ++ [last]) base (last.imageOffset + index) =
      some (wordByte (base + last.addend) index) := by
  simp only [relocatedImage, List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyRelative_byte base _ last index bound

#print axioms patches_frame
#print axioms patches_append
#print axioms applyRelative_commute
#print axioms patches_frame_slot
#print axioms relocatedImage_unpatched
#print axioms relocatedImage_last_patch

end MemReloc
