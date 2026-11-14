import ArmCertTranslateModel.StaticPieChecker
import ArmCertTranslateModel.HeapV2Initial

/-! Decision-136 checker THEOREM. For raw ELF bytes the executable checker `check`
admits (unchanged; `heapv2_check` still holds by rfl):
* the file is a little-endian ELF64 AArch64 ET_DYN with DF_1_PIE, and every PT_LOAD's
  file bytes lie inside the file;
* there is no DT_REL, DT_TEXTREL, DT_JMPREL or DT_RELR table, so the only dynamic
  relocation table is DT_RELA;
* every DT_RELA entry has ELF64_R_TYPE = R_AARCH64_RELATIVE (1027). In particular none is
  IRELATIVE, GLOB_DAT, JUMP_SLOT or a TLS type;
* the returned segments and patches are exactly the PT_LOADs (header order) and the RELA
  entries (table order);
* for every load base B, the `referenceImage`, written directly from raw headers and
  RELA entries with ELF/AArch64-ABI RELATIVE semantics (8 LE bytes of B + r_addend mod 2^64
  at r_offset), equals C9's `relocatedImage`.
Scope: the single PT_DYNAMIC and the first occurrence of each dynamic tag, as read by
`dynamicValue`. No OS-loader or self-relocator implementation correctness is claimed. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace ArmCert.Translate.Model.StaticPie

/-- Raw ELF64 RELA entry. -/
structure Rela where
  offset : Nat
  info : Nat
  addend : Nat
  deriving DecidableEq, Repr

/-- ELF64_R_TYPE. -/
def Rela.type (r : Rela) : Nat := r.info % 4294967296

def R_AARCH64_RELATIVE : Nat := 1027

/-- The C9 patch denoted by a RELATIVE entry (link base 0: image offset = r_offset). -/
def Rela.patch (r : Rela) : MemReloc.RelativePatch := ⟨r.offset, BitVec.ofNat 64 r.addend⟩

def relaRow (bytes : Array Nat) (start index : Nat) : Rela :=
  ⟨u64 bytes (start + 24 * index), u64 bytes (start + 24 * index + 8), u64 bytes (start + 24 * index + 16)⟩

/-- The whole DT_RELA table as a loader reads it, with every entry of any type; `none` when
    DT_RELA/DT_RELASZ are not both present or both absent, or the table is outside every PT_LOAD. -/
def relaTable (bytes : Array Nat) : Option (List Rela) :=
  match dynamicValue bytes 7, dynamicValue bytes 8 with
  | none, none => some []
  | some address, some total =>
    (fileOffset bytes address).map fun start => (List.range (total / 24)).map (relaRow bytes start)
  | _, _ => none

/-- The ELF file as a C9 image indexed by file offset. -/
def fileImage (bytes : Array Nat) : MemReloc.Image := fun offset => (bytes[offset]?).map (BitVec.ofNat 8)

def normalize (header : ProgramHeader) : MemReloc.LoadSegment :=
  ⟨header.offset, header.vaddr, header.fileSize, header.memorySize⟩

/-- Map one PT_LOAD: its file bytes, then zero fill to p_memsz; other bytes unchanged. -/
def mapLoad (bytes : Array Nat) (previous : MemReloc.Image) (header : ProgramHeader) :
    MemReloc.Image := fun offset =>
  if header.vaddr ≤ offset ∧ offset < header.vaddr + header.memorySize then
    if offset - header.vaddr < header.fileSize then
      some (BitVec.ofNat 8 (byte bytes (header.offset + (offset - header.vaddr))))
    else some 0
  else previous offset

/-- R_AARCH64_RELATIVE: the 8 bytes at r_offset receive B + r_addend (mod 2^64), little-endian. -/
def relocate (base : MemReloc.Word) (previous : MemReloc.Image) (r : Rela) : MemReloc.Image :=
  fun offset =>
    if r.offset ≤ offset ∧ offset < r.offset + 8 then
      some ((BitVec.ofNat 64 (base.toNat + r.addend)).extractLsb' (8 * (offset - r.offset)) 8)
    else previous offset

/-- Reference loader image at base B: PT_LOADs in header order, then RELA entries in order. -/
def referenceImage (bytes : Array Nat) (base : MemReloc.Word) : MemReloc.Image :=
  ((relaTable bytes).getD []).foldl (relocate base) ((loads bytes).foldl (mapLoad bytes) fun _ => none)

/-! ### Checker decomposition -/

def relStep (entry : Nat × Nat × Nat) (rest : Option (List MemReloc.RelativePatch)) :
    Option (List MemReloc.RelativePatch) :=
  if entry.2.1 == 1027 then rest.map (⟨entry.1, BitVec.ofNat 64 entry.2.2⟩ :: ·) else none

theorem foldr_relative : ∀ (l : List (Nat × Nat × Nat)) (ps : List MemReloc.RelativePatch),
    l.foldr relStep (some []) = some ps →
    (∀ e ∈ l, e.2.1 = 1027) ∧
      ps = l.map fun e => (⟨e.1, BitVec.ofNat 64 e.2.2⟩ : MemReloc.RelativePatch)
  | [], ps, h => by
    simp only [List.foldr_nil, Option.some.injEq] at h
    subst h
    simp
  | e :: l, ps, h => by
    cases hr : l.foldr relStep (some []) with
    | none =>
      rw [List.foldr_cons, hr] at h
      simp [relStep] at h
    | some rest =>
      rw [List.foldr_cons, hr] at h
      obtain ⟨all, eq⟩ := foldr_relative l rest hr
      simp only [relStep] at h
      split at h
      · next he =>
        simp only [Option.map, Option.some.injEq] at h
        subst h
        refine ⟨?_, ?_⟩
        · intro x mem
          rcases List.mem_cons.mp mem with rfl | mem
          · simpa using he
          · exact all x mem
        · rw [eq]; rfl
      · cases h

theorem relativePatches_sound {bytes : Array Nat} {ps : List MemReloc.RelativePatch}
    (h : relativePatches bytes = some ps) :
    (∀ tag ∈ [17, 22, 23, 36], dynamicValue bytes tag = none) ∧
    ∃ table, relaTable bytes = some table ∧ (∀ r ∈ table, r.type = R_AARCH64_RELATIVE) ∧
      ps = table.map Rela.patch := by
  unfold relativePatches at h
  split at h
  · cases h
  · next forbidden =>
    refine ⟨?_, ?_⟩
    · intro tag mem
      cases hv : dynamicValue bytes tag with
      | none => rfl
      | some v =>
        exfalso
        exact forbidden (List.any_eq_true.mpr ⟨tag, mem, by simp [hv]⟩)
    · split at h
      · next h7 h8 =>
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨[], by simp [relaTable, h7, h8], by simp, rfl⟩
      · next address total h7 h8 =>
        split at h
        · cases h
        · next start hstart =>
          obtain ⟨all, eq⟩ := foldr_relative _ _ h
          refine ⟨(List.range (total / 24)).map (relaRow bytes start), by simp [relaTable, h7, h8, hstart], ?_, ?_⟩
          · intro r mem
            exact all (r.offset, r.type, r.addend) (by
              rw [List.mem_map]
              obtain ⟨index, imem, rfl⟩ := List.mem_map.mp mem
              exact ⟨index, imem, rfl⟩)
          · rw [eq, List.map_map, List.map_map]; rfl
      · cases h

/-! ### Reference loader = C9 -/

theorem mapLoad_eq {bytes : Array Nat} (previous : MemReloc.Image) (header : ProgramHeader)
    (bound : header.offset + header.fileSize ≤ bytes.size) :
    mapLoad bytes previous header = MemReloc.loadSegment (fileImage bytes) previous (normalize header) := by
  obtain ⟨kind, flags, fileOff, vaddr, fileSize, memorySize⟩ := header
  funext offset
  dsimp only [mapLoad, MemReloc.loadSegment, normalize]
  by_cases c1 : vaddr ≤ offset ∧ offset < vaddr + memorySize
  · rw [ite_cond_eq_true _ _ (eq_true c1), ite_cond_eq_true _ _ (eq_true c1)]
    by_cases c2 : offset - vaddr < fileSize
    · rw [ite_cond_eq_true _ _ (eq_true c2), ite_cond_eq_true _ _ (eq_true c2)]
      have hi : fileOff + (offset - vaddr) < bytes.size := by simp only at bound; omega
      simp [fileImage, byte, Array.getD, hi]
    · rw [ite_cond_eq_false _ _ (eq_false c2), ite_cond_eq_false _ _ (eq_false c2)]
  · rw [ite_cond_eq_false _ _ (eq_false c1), ite_cond_eq_false _ _ (eq_false c1)]

theorem loads_eq (bytes : Array Nat) : ∀ (l : List ProgramHeader) (init : MemReloc.Image),
    (∀ header ∈ l, header.offset + header.fileSize ≤ bytes.size) →
    l.foldl (mapLoad bytes) init = (l.map normalize).foldl (MemReloc.loadSegment (fileImage bytes)) init
  | [], _, _ => rfl
  | header :: l, init, bound => by
    simp only [List.foldl_cons, List.map_cons]
    rw [mapLoad_eq init header (bound header List.mem_cons_self)]
    exact loads_eq bytes l _ (fun x mem => bound x (List.mem_cons_of_mem header mem))

theorem relocate_eq (base : MemReloc.Word) (previous : MemReloc.Image) (r : Rela) :
    relocate base previous r = MemReloc.applyRelative base previous r.patch := by
  have word : BitVec.ofNat 64 (base.toNat + r.addend) = base + BitVec.ofNat 64 r.addend := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add]
  funext offset
  simp only [relocate, MemReloc.applyRelative, Rela.patch, MemReloc.wordByte, word]
  rfl

theorem relocs_eq (base : MemReloc.Word) : ∀ (table : List Rela) (init : MemReloc.Image),
    table.foldl (relocate base) init = (table.map Rela.patch).foldl (MemReloc.applyRelative base) init
  | [], _ => rfl
  | r :: table, init => by
    simp only [List.foldl_cons, List.map_cons]
    rw [relocate_eq base init r]
    exact relocs_eq base table _

/-! ### The checker theorem -/

/-- What decision-136 admission guarantees about raw ELF bytes. -/
structure Admitted (bytes : Array Nat) (segments : List MemReloc.LoadSegment)
    (patches : List MemReloc.RelativePatch) : Prop where
  header : headerOK bytes = true
  loadsInFile : ∀ header ∈ loads bytes, header.offset + header.fileSize ≤ bytes.size ∧
    header.fileSize ≤ header.memorySize
  pie : pieFlag bytes = true
  noOtherTables : ∀ tag ∈ [17, 22, 23, 36], dynamicValue bytes tag = none
  relativeOnly : ∃ table, relaTable bytes = some table ∧
    (∀ r ∈ table, r.type = R_AARCH64_RELATIVE) ∧ patches = table.map Rela.patch
  segmentsExact : segments = (loads bytes).map normalize
  image : ∀ base, referenceImage bytes base = MemReloc.relocatedImage (fileImage bytes) segments patches base

theorem check_sound {bytes : Array Nat} {segments : List MemReloc.LoadSegment}
    {patches : List MemReloc.RelativePatch} (h : check bytes = some (segments, patches)) :
    Admitted bytes segments patches := by
  unfold check at h
  split at h
  · next ok =>
    simp only [Bool.and_eq_true] at ok
    obtain ⟨⟨hh, hl⟩, hp⟩ := ok
    cases hr : relativePatches bytes with
    | none => rw [hr] at h; cases h
    | some ps =>
      rw [hr] at h
      simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hs, hps⟩ := h
      subst hs hps
      obtain ⟨none, table, ht, rel, eq⟩ := relativePatches_sound hr
      have bounds : ∀ header ∈ loads bytes, header.offset + header.fileSize ≤ bytes.size ∧
          header.fileSize ≤ header.memorySize := by
        intro header mem
        have := List.all_eq_true.mp hl header mem
        simpa using this
      refine ⟨hh, bounds, hp, none, ⟨table, ht, rel, eq⟩, rfl, ?_⟩
      intro base
      simp only [referenceImage, MemReloc.relocatedImage, MemReloc.loadSegments, ht,
        Option.getD_some]
      rw [loads_eq bytes _ _ (fun header mem => (bounds header mem).1), relocs_eq, eq]
      rfl
  · cases h

/-- Corollary: no admitted relocation is IRELATIVE, GLOB_DAT, JUMP_SLOT or a TLS type. -/
theorem admitted_excludes {bytes : Array Nat} {segments : List MemReloc.LoadSegment}
    {patches : List MemReloc.RelativePatch} (admitted : Admitted bytes segments patches) :
    ∃ table, relaTable bytes = some table ∧
      ∀ r ∈ table, r.type ∉ [1025, 1026, 1028, 1029, 1030, 1031, 1032] := by
  obtain ⟨table, ht, rel, _⟩ := admitted.relativeOnly
  exact ⟨table, ht, fun r mem => by rw [rel r mem]; decide⟩

/-! ### heap-v2 instance (C9 link) -/

theorem heapv2_admitted : Admitted HeapV2.fileBytes HeapV2.segments HeapV2.patches :=
  check_sound heapv2_check

theorem heapv2_file : fileImage HeapV2.fileBytes = HeapV2.file := rfl

/-- The C9 heap-v2 image used by placement (`HeapV2.image`, `initState_image_on`) is the
    reference loader's image of the raw ELF at every load base. -/
theorem heapv2_image_reference (base : MemReloc.Word) :
    HeapV2.image base = referenceImage HeapV2.fileBytes base := by
  rw [heapv2_admitted.image base, heapv2_file]
  rfl

#print axioms foldr_relative
#print axioms relativePatches_sound
#print axioms check_sound
#print axioms admitted_excludes
#print axioms heapv2_admitted
#print axioms heapv2_image_reference
end ArmCert.Translate.Model.StaticPie
