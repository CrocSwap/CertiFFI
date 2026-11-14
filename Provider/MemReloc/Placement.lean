import MemReloc.Image
import ArmFull

namespace MemReloc

open Sail Sail.ConcurrencyInterfaceV1 ArmFull

abbrev NativeState := SequentialState Regs oracleChoiceSource
abbrev Mapping := Word → Option Nat

def imageAddress (base : Word) (offset : Nat) : Word := base + BitVec.ofNat 64 offset

/-- The approved C9 deployment bounds, kept explicit and separate from byte
    placement and caller/source provenance. Page size is an input. -/
structure PlacementBounds (base : Word) (span pageBytes : Nat) : Prop where
  basePositive : 0 < base.toNat
  pagePositive : 0 < pageBytes
  aligned : base.toNat % pageBytes = 0
  noWrap : base.toNat + span ≤ 2 ^ 64

theorem imageAddress_toNat {base : Word} {span pageBytes offset : Nat}
    (bounds : PlacementBounds base span pageBytes) (member : offset < span) :
    (imageAddress base offset).toNat = base.toNat + offset := by
  have offsetBound : offset < 2 ^ 64 := by have := bounds.noWrap; omega
  have offsetValue : (BitVec.ofNat 64 offset).toNat = offset := by
    change offset % 2 ^ 64 = offset
    exact Nat.mod_eq_of_lt offsetBound
  have sumBound : base.toNat + (BitVec.ofNat 64 offset).toNat < 2 ^ 64 := by
    rw [offsetValue]
    have := bounds.noWrap
    omega
  simpa only [imageAddress, offsetValue] using BitVec.toNat_add_of_lt sumBound

/-- IMAGE membership and approved placement bounds derive nonzero. PLAIN
    caller values (including null) are not constrained by this lemma. -/
theorem imageAddress_nonzero {base : Word} {span pageBytes offset : Nat}
    (bounds : PlacementBounds base span pageBytes) (member : offset < span) :
    imageAddress base offset ≠ 0 := by
  have value := imageAddress_toNat bounds member
  have positive := bounds.basePositive
  intro zero
  have zeroNat : (imageAddress base offset).toNat = 0 := by rw [zero]; rfl
  omega

def ImageEqOn (scope : Nat → Prop) (left right : Image) : Prop :=
  ∀ offset, scope offset → left offset = right offset

/-- Both image presence and actual native physical presence are required. -/
def ImageOn (scope : Nat → Prop) (image : Image) (state : NativeState)
    (base : Word) (mapping : Mapping) : Prop :=
  ∀ offset, scope offset → ∃ byte pa,
    image offset = some byte ∧ mapping (imageAddress base offset) = some pa ∧
      state.mem[pa]? = some byte

/-- Startup C9 postcondition for a normalized image. A consumer's immutable
    image scope must be transported through proved caller/runtime updates.
    Mutable IMAGE-backed caller payload is supplied by its source/heap relation,
    not forced to equal these startup file/BSS bytes. Raw ELF binding, source
    pointer roles, placement bounds and future preservation remain separate. -/
def C9 (scope : Nat → Prop) (file : Image) (segments : List LoadSegment)
    (patches : List RelativePatch) (base : Word) (state : NativeState)
    (mapping : Mapping) : Prop :=
  ImageOn scope (relocatedImage file segments patches base) state base mapping

theorem imageOn_byte {scope : Nat → Prop} {image : Image} {state : NativeState}
    {base : Word} {mapping : Mapping} (placed : ImageOn scope image state base mapping)
    {offset : Nat} (inside : scope offset) {byte : Byte} (value : image offset = some byte) :
    ∃ pa, mapping (imageAddress base offset) = some pa ∧ state.mem[pa]? = some byte := by
  obtain ⟨actual, pa, hi, hm, hp⟩ := placed offset inside
  have eq : actual = byte := Option.some.inj (hi.symm.trans value)
  exact ⟨pa, hm, eq ▸ hp⟩

/-- C9 equality is restricted to the supplied certified closure. -/
theorem imageOn_of_eq {scope : Nat → Prop} {left right : Image} {state : NativeState}
    {base : Word} {mapping : Mapping} (equal : ImageEqOn scope left right)
    (placed : ImageOn scope left state base mapping) :
    ImageOn scope right state base mapping := by
  intro offset inside
  obtain ⟨byte, pa, hi, hm, hp⟩ := placed offset inside
  exact ⟨byte, pa, (equal offset inside).symm.trans hi, hm, hp⟩

theorem imageOn_mono {scope small : Nat → Prop} {image : Image} {state : NativeState}
    {base : Word} {mapping : Mapping} (placed : ImageOn scope image state base mapping)
    (subset : ∀ offset, small offset → scope offset) :
    ImageOn small image state base mapping := by
  intro offset inside
  exact placed offset (subset offset inside)

/-- Current-memory transport only; this is not a future execution premise. -/
theorem imageOn_memory {scope : Nat → Prop} {image : Image} {left right : NativeState}
    {base : Word} {mapping : Mapping} (placed : ImageOn scope image left base mapping)
    (memory : right.mem = left.mem) : ImageOn scope image right base mapping := by
  intro offset inside
  obtain ⟨byte, pa, hi, hm, hp⟩ := placed offset inside
  exact ⟨byte, pa, hi, hm, by rw [memory]; exact hp⟩

/-- Pointwise byte equality on the explicit mapped image scope. This describes
    two current memories; it does not supply future translation answers. The
    caller/native update proofs must establish this relation internally. -/
def ScopeMemoryEq (scope : Nat → Prop) (base : Word) (mapping : Mapping)
    (left right : NativeState) : Prop :=
  ∀ offset pa, scope offset → mapping (imageAddress base offset) = some pa →
    right.mem[pa]? = left.mem[pa]?

/-- Transport an immutable image scope without equality of unrelated memory.
    In particular mutable caller payload can lie outside this scope. -/
theorem imageOn_frame {scope : Nat → Prop} {image : Image} {left right : NativeState}
    {base : Word} {mapping : Mapping} (placed : ImageOn scope image left base mapping)
    (frame : ScopeMemoryEq scope base mapping left right) :
    ImageOn scope image right base mapping := by
  intro offset inside
  obtain ⟨byte, pa, hi, hm, hp⟩ := placed offset inside
  exact ⟨byte, pa, hi, hm, (frame offset pa inside hm).trans hp⟩

/-- Narrow startup placement to the immutable consumer scope, then transport
    it across the proved updates. No equality is imposed on excluded payload. -/
theorem c9_consumer_frame {startupScope immutableScope : Nat → Prop} {file : Image}
    {segments : List LoadSegment} {patches : List RelativePatch} {base : Word}
    {startup consumer : NativeState} {mapping : Mapping}
    (placed : C9 startupScope file segments patches base startup mapping)
    (subset : ∀ offset, immutableScope offset → startupScope offset)
    (frame : ScopeMemoryEq immutableScope base mapping startup consumer) :
    ImageOn immutableScope (relocatedImage file segments patches base) consumer base mapping := by
  exact imageOn_frame (imageOn_mono placed subset) frame

/-- The mapping-to-native bridge retains the actual translated physical address. -/
theorem imageOn_translated_byte {scope : Nat → Prop} {image : Image} {state : NativeState}
    {base : Word} {mapping : Mapping} (placed : ImageOn scope image state base mapping)
    {offset pa : Nat} (inside : scope offset) (mapped : mapping (imageAddress base offset) = some pa)
    {byte : Byte} (value : image offset = some byte) : state.mem[pa]? = some byte := by
  obtain ⟨actual, hm, hp⟩ := imageOn_byte placed inside value
  have eq : actual = pa := Option.some.inj (hm.symm.trans mapped)
  exact eq ▸ hp

theorem c9_last_patch_byte {scope : Nat → Prop} {file : Image}
    {segments : List LoadSegment} {patches : List RelativePatch} {last : RelativePatch}
    {base : Word} {state : NativeState} {mapping : Mapping} {index pa : Nat}
    (placed : C9 scope file segments (patches ++ [last]) base state mapping)
    (inside : scope (last.imageOffset + index)) (bound : index < 8)
    (mapped : mapping (imageAddress base (last.imageOffset + index)) = some pa) :
    state.mem[pa]? = some (wordByte (base + last.addend) index) := by
  exact imageOn_translated_byte placed inside mapped
    (relocatedImage_last_patch file segments patches last base index bound)

#print axioms imageAddress_toNat
#print axioms imageAddress_nonzero
#print axioms imageOn_byte
#print axioms imageOn_of_eq
#print axioms imageOn_mono
#print axioms imageOn_memory
#print axioms imageOn_frame
#print axioms c9_consumer_frame
#print axioms imageOn_translated_byte
#print axioms c9_last_patch_byte

end MemReloc
