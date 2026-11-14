import ArmCertTranslateModel.StaticPieSound

/-! a design decision: the CLOSURE-SCOPED static-PIE checker theorem, an additive
extension of StaticPieSound (heap-v2's `check_sound` is unchanged).

Admission: every DT_RELA entry is R_AARCH64_RELATIVE, OR R_AARCH64_IRELATIVE with its 8-byte slot outside every
certified byte (the closure's fetched code and its static-image reads) and its resolver outside the certified code.
IRELATIVE slots are left unconstrained: the reference loader writes an arbitrary resolver result `ifunc addend`
there, and nothing is claimed about those bytes.

Proof route (a): the theorem is stated over structured SLICES of the ELF (file size, the 64 header bytes, the
program headers, the dynamic entries, the RELA rows). `Binds bytes sl` says the slices are those of the file; it
is established outside Lean by the sha-pinned slice generator (final_binding-style byte-range binding). Every
admission check is decided on the slices, so a large ELF needs no kernel evaluation of its bytes; instances
check the RELA rows chunk by chunk.

Conclusion (`scoped_sound`): the header/PT_LOAD/PIE/no-other-table facts about the file, the scoped RELA facts,
and, for every load base, every resolver result function and every certified byte x, the reference loader image
at x equals C9's relocatedImage of the file with the PT_LOADs and the RELATIVE patches. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace ArmCert.Translate.Model.StaticPie

def R_AARCH64_IRELATIVE : Nat := 1032

/-! ### Closure and the scoped admission rule -/

/-- Certified closure in image offsets (link base 0): `[lo, hi)` code ranges (fetched words) and static-image
    read ranges. -/
structure Closure where
  code : List (Nat × Nat)
  reads : List (Nat × Nat)
  deriving Repr

def inRanges (ranges : List (Nat × Nat)) (x : Nat) : Bool := ranges.any fun r => decide (r.1 ≤ x ∧ x < r.2)

/-- A certified byte: fetched by the closure or read by it from the static image. -/
def Closure.Covers (c : Closure) (x : Nat) : Prop := inRanges c.code x = true ∨ inRanges c.reads x = true

/-- The 8-byte slot [offset, offset+8) avoids every certified range. -/
def slotClear (c : Closure) (r : Rela) : Bool :=
  (c.code ++ c.reads).all fun iv => decide (r.offset + 8 ≤ iv.1 ∨ iv.2 ≤ r.offset)

def entryOK (c : Closure) (r : Rela) : Bool :=
  r.type == R_AARCH64_RELATIVE ||
    (r.type == R_AARCH64_IRELATIVE && slotClear c r && !(inRanges c.code r.addend))

theorem slotClear_sound {c : Closure} {r : Rela} (h : slotClear c r = true) (x : Nat)
    (inSlot : r.offset ≤ x ∧ x < r.offset + 8) : ¬ c.Covers x := by
  intro cover
  have all := List.all_eq_true.1 h
  rcases cover with hc | hr
  · obtain ⟨iv, member, hiv⟩ := List.any_eq_true.1 hc
    have := all iv (List.mem_append_left _ member)
    simp only [decide_eq_true_eq] at this hiv
    omega
  · obtain ⟨iv, member, hiv⟩ := List.any_eq_true.1 hr
    have := all iv (List.mem_append_right _ member)
    simp only [decide_eq_true_eq] at this hiv
    omega

/-! ### Reference loader with IRELATIVE (unconstrained resolver results) -/

/-- RELATIVE writes B + addend; IRELATIVE writes the resolver result `ifunc addend` (arbitrary). Both write the
    8 little-endian bytes at r_offset. -/
def relocateI (base : MemReloc.Word) (ifunc : Nat → MemReloc.Word) (previous : MemReloc.Image)
    (r : Rela) : MemReloc.Image := fun offset =>
  if r.offset ≤ offset ∧ offset < r.offset + 8 then
    if r.type = R_AARCH64_IRELATIVE then some ((ifunc r.addend).extractLsb' (8 * (offset - r.offset)) 8)
    else some ((BitVec.ofNat 64 (base.toNat + r.addend)).extractLsb' (8 * (offset - r.offset)) 8)
  else previous offset

def referenceImageI (bytes : Array Nat) (base : MemReloc.Word) (ifunc : Nat → MemReloc.Word) :
    MemReloc.Image :=
  ((relaTable bytes).getD []).foldl (relocateI base ifunc) ((loads bytes).foldl (mapLoad bytes) fun _ => none)

/-- The RELATIVE patches of a RELA table. -/
def relativePatchesOf (table : List Rela) : List MemReloc.RelativePatch :=
  (table.filter (·.type == R_AARCH64_RELATIVE)).map Rela.patch

/-- Pointwise: away from every IRELATIVE slot, folding all entries with `relocateI` equals folding the RELATIVE
    entries with `relocate`, from images that agree at `x`. -/
theorem fold_scoped (base : MemReloc.Word) (ifunc : Nat → MemReloc.Word) (x : Nat) :
    ∀ (l : List Rela) (i j : MemReloc.Image), i x = j x →
      (∀ r ∈ l, r.type = R_AARCH64_RELATIVE ∨
        (r.type = R_AARCH64_IRELATIVE ∧ ¬ (r.offset ≤ x ∧ x < r.offset + 8))) →
      (l.foldl (relocateI base ifunc) i) x = ((l.filter (·.type == R_AARCH64_RELATIVE)).foldl (relocate base) j) x
  | [], _, _, h, _ => h
  | r :: l, i, j, h, rows => by
    have rest : ∀ r' ∈ l, r'.type = R_AARCH64_RELATIVE ∨
        (r'.type = R_AARCH64_IRELATIVE ∧ ¬ (r'.offset ≤ x ∧ x < r'.offset + 8)) :=
      fun r' m => rows r' (List.mem_cons_of_mem r m)
    rcases rows r List.mem_cons_self with rel | ⟨irel, outside⟩
    · have keep : (r.type == R_AARCH64_RELATIVE) = true := by simp [rel]
      rw [List.foldl_cons, List.filter_cons_of_pos (p := fun x : Rela => x.type == R_AARCH64_RELATIVE) keep, List.foldl_cons]
      apply fold_scoped base ifunc x l _ _ _ rest
      have notI : ¬ r.type = R_AARCH64_IRELATIVE := by rw [rel]; decide
      simp only [relocateI, relocate, notI, ite_false]
      split
      · rfl
      · exact h
    · have drop : ¬ (r.type == R_AARCH64_RELATIVE) = true := by simp [irel, R_AARCH64_IRELATIVE, R_AARCH64_RELATIVE]
      rw [List.foldl_cons, List.filter_cons_of_neg (p := fun x : Rela => x.type == R_AARCH64_RELATIVE) drop]
      apply fold_scoped base ifunc x l _ _ _ rest
      simp only [relocateI, outside, ite_false]
      exact h

/-! ### Slices and their binding to the file -/

structure Slices where
  size : Nat
  header : List Nat
  phdrs : List ProgramHeader
  dynamic : List (Nat × Nat)
  rela : List Rela

/-- The slices are those of the file. Established outside Lean by the sha-pinned slice generator. -/
structure Binds (bytes : Array Nat) (sl : Slices) : Prop where
  size : bytes.size = sl.size
  header : ∀ i < 64, byte bytes i = sl.header.getD i 0
  phdrs : programHeaders bytes = sl.phdrs
  dynamic : dynamicEntries bytes = sl.dynamic
  rela : relaTable bytes = some sl.rela

def sByte (sl : Slices) (i : Nat) : Nat := sl.header.getD i 0
def sU16 (sl : Slices) (i : Nat) : Nat := sByte sl i + 256 * sByte sl (i + 1)
def sU32 (sl : Slices) (i : Nat) : Nat := sU16 sl i + 65536 * sU16 sl (i + 2)
def sU64 (sl : Slices) (i : Nat) : Nat := sU32 sl i + 4294967296 * sU32 sl (i + 4)

/-- `headerOK` decided on the slices. -/
def headerOKS (sl : Slices) : Bool :=
  decide (64 ≤ sl.size) && sByte sl 0 == 0x7f && sByte sl 1 == 0x45 && sByte sl 2 == 0x4c &&
  sByte sl 3 == 0x46 && sByte sl 4 == 2 && sByte sl 5 == 1 && sU16 sl 0x10 == 3 &&
  sU16 sl 0x12 == 0xb7 && sU16 sl 0x36 == 56 &&
  decide (sU64 sl 0x20 + sU16 sl 0x38 * 56 ≤ sl.size)

def loadsS (sl : Slices) : List ProgramHeader := sl.phdrs.filter (·.kind == 1)

def loadsOKS (sl : Slices) : Bool :=
  (loadsS sl).all fun header =>
    decide (header.offset + header.fileSize ≤ sl.size) && decide (header.fileSize ≤ header.memorySize)

def dynamicValueS (sl : Slices) (tag : Nat) : Option Nat := (sl.dynamic.find? (·.1 == tag)).map (·.2)

def pieFlagS (sl : Slices) : Bool :=
  match dynamicValueS sl 0x6ffffffb with
  | some flags => (flags / 0x8000000) % 2 == 1
  | none => false

/-- The non-row admission checks, decided on the slices. -/
def frameOKS (sl : Slices) : Bool :=
  headerOKS sl && loadsOKS sl && pieFlagS sl && [17, 22, 23, 36].all fun tag => (dynamicValueS sl tag).isNone

theorem headerOK_of_binds {bytes : Array Nat} {sl : Slices} (b : Binds bytes sl) :
    headerOK bytes = headerOKS sl := by
  have hb : ∀ i, i < 64 → byte bytes i = sByte sl i := fun i h => b.header i h
  simp only [headerOK, headerOKS, u64, u32, u16, sU64, sU32, sU16, b.size]
  simp only [hb 0 (by decide), hb 1 (by decide), hb 2 (by decide), hb 3 (by decide), hb 4 (by decide),
    hb 5 (by decide), hb 0x10 (by decide), hb 0x11 (by decide), hb 0x12 (by decide), hb 0x13 (by decide),
    hb 0x36 (by decide), hb 0x37 (by decide), hb 0x38 (by decide), hb 0x39 (by decide), hb 0x20 (by decide),
    hb 0x21 (by decide), hb 0x22 (by decide), hb 0x23 (by decide), hb 0x24 (by decide), hb 0x25 (by decide),
    hb 0x26 (by decide), hb 0x27 (by decide), Nat.reduceAdd]
  rfl

theorem loads_of_binds {bytes : Array Nat} {sl : Slices} (b : Binds bytes sl) : loads bytes = loadsS sl := by
  simp only [loads, loadsS, b.phdrs]

theorem loadsOK_of_binds {bytes : Array Nat} {sl : Slices} (b : Binds bytes sl) : loadsOK bytes = loadsOKS sl := by
  simp only [loadsOK, loadsOKS, loads_of_binds b, b.size]

theorem dynamicValue_of_binds {bytes : Array Nat} {sl : Slices} (b : Binds bytes sl) (tag : Nat) :
    dynamicValue bytes tag = dynamicValueS sl tag := by
  simp only [dynamicValue, dynamicValueS, b.dynamic]

theorem pieFlag_of_binds {bytes : Array Nat} {sl : Slices} (b : Binds bytes sl) : pieFlag bytes = pieFlagS sl := by
  simp only [pieFlag, pieFlagS, dynamicValue_of_binds b]
  rfl

/-! ### The scoped checker theorem -/

structure ScopedAdmitted (bytes : Array Nat) (c : Closure) (table : List Rela) : Prop where
  header : headerOK bytes = true
  loadsInFile : ∀ header ∈ loads bytes, header.offset + header.fileSize ≤ bytes.size ∧
    header.fileSize ≤ header.memorySize
  pie : pieFlag bytes = true
  noOtherTables : ∀ tag ∈ [17, 22, 23, 36], dynamicValue bytes tag = none
  relaIs : relaTable bytes = some table
  relaScoped : ∀ r ∈ table, r.type = R_AARCH64_RELATIVE ∨
    (r.type = R_AARCH64_IRELATIVE ∧ (∀ x, r.offset ≤ x → x < r.offset + 8 → ¬ c.Covers x) ∧
      inRanges c.code r.addend = false)
  image : ∀ (base : MemReloc.Word) (ifunc : Nat → MemReloc.Word) (x : Nat), c.Covers x →
    referenceImageI bytes base ifunc x =
      MemReloc.relocatedImage (fileImage bytes) ((loads bytes).map normalize) (relativePatchesOf table) base x

theorem scoped_sound {bytes : Array Nat} {sl : Slices} (c : Closure) (b : Binds bytes sl)
    (frame : frameOKS sl = true) (rows : ∀ r ∈ sl.rela, entryOK c r = true) :
    ScopedAdmitted bytes c sl.rela := by
  simp only [frameOKS, Bool.and_eq_true] at frame
  obtain ⟨⟨⟨hh, hl⟩, hp⟩, hn⟩ := frame
  have bounds : ∀ header ∈ loads bytes, header.offset + header.fileSize ≤ bytes.size ∧
      header.fileSize ≤ header.memorySize := by
    rw [← loadsOK_of_binds b] at hl
    intro header member
    have := List.all_eq_true.1 hl header member
    simpa using this
  have relaScoped : ∀ r ∈ sl.rela, r.type = R_AARCH64_RELATIVE ∨
      (r.type = R_AARCH64_IRELATIVE ∧ (∀ x, r.offset ≤ x → x < r.offset + 8 → ¬ c.Covers x) ∧
        inRanges c.code r.addend = false) := by
    intro r member
    have ok := rows r member
    simp only [entryOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at ok
    rcases ok with rel | ⟨⟨irel, clear⟩, code⟩
    · exact Or.inl rel
    · exact Or.inr ⟨irel, fun x lo hi => slotClear_sound clear x ⟨lo, hi⟩, code⟩
  refine ⟨(headerOK_of_binds b).trans hh, bounds, (pieFlag_of_binds b).trans hp, ?_, b.rela, relaScoped, ?_⟩
  · intro tag member
    rw [dynamicValue_of_binds b]
    have := List.all_eq_true.1 hn tag member
    simpa using this
  · intro base ifunc x cover
    simp only [referenceImageI, b.rela, Option.getD_some, MemReloc.relocatedImage, MemReloc.loadSegments,
      relativePatchesOf]
    rw [loads_eq bytes _ _ (fun header member => (bounds header member).1), ← relocs_eq]
    apply fold_scoped base ifunc x sl.rela _ _ rfl
    intro r member
    rcases relaScoped r member with rel | ⟨irel, clear, _⟩
    · exact Or.inl rel
    · exact Or.inr ⟨irel, fun ⟨lo, hi⟩ => clear x lo hi cover⟩

#print axioms fold_scoped
#print axioms headerOK_of_binds
#print axioms scoped_sound
end ArmCert.Translate.Model.StaticPie
