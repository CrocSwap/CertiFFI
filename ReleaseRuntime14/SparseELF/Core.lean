import ArmCertTranslateModel.StaticPieScoped
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace SparseELF
open ArmCert.Translate.Model.StaticPie

/-- A concrete array, kept symbolic through getElem_ofFn instead of expanding millions of cells. -/
def bytesOf (size : Nat) (f : Nat → Nat) : Array Nat := Array.ofFn fun i : Fin size => f i.val

theorem bytesOf_size (size : Nat) (f : Nat → Nat) : (bytesOf size f).size = size := by simp [bytesOf]

theorem byte_bytesOf (size : Nat) (f : Nat → Nat) (i : Nat) (hi : i < size) :
    byte (bytesOf size f) i = f i := by
  simp [byte, bytesOf, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi]

def digit (value index : Nat) : Nat := value / 256 ^ index % 256

theorem decode8 (v : Nat) (bound : v < 2 ^ 64) :
    digit v 0 + 256*digit v 1 + 65536*(digit v 2 + 256*digit v 3) +
      4294967296*(digit v 4 + 256*digit v 5 + 65536*(digit v 6 + 256*digit v 7)) = v := by
  simp only [digit, Nat.pow_zero, Nat.div_one, Nat.pow_one]
  omega

def totalByte (size : Nat) (f : Nat → Nat) (i : Nat) : Nat := if i < size then f i else 0

theorem byte_bytesOf_all (size : Nat) (f : Nat → Nat) (i : Nat) :
    byte (bytesOf size f) i = totalByte size f i := by
  by_cases h : i < size
  · simp [totalByte, byte_bytesOf, h]
  · simp [byte, bytesOf, totalByte, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, h]

def read16 (f : Nat → Nat) (i : Nat) : Nat := f i + 256*f (i+1)
def read32 (f : Nat → Nat) (i : Nat) : Nat := read16 f i + 65536*read16 f (i+2)
def read64 (f : Nat → Nat) (i : Nat) : Nat := read32 f i + 4294967296*read32 f (i+4)

theorem u16_bytesOf (size : Nat) (f : Nat → Nat) (i : Nat) :
    u16 (bytesOf size f) i = read16 (totalByte size f) i := by simp only [u16, read16, byte_bytesOf_all]
theorem u32_bytesOf (size : Nat) (f : Nat → Nat) (i : Nat) :
    u32 (bytesOf size f) i = read32 (totalByte size f) i := by simp only [u32, read32, u16_bytesOf]
theorem u64_bytesOf (size : Nat) (f : Nat → Nat) (i : Nat) :
    u64 (bytesOf size f) i = read64 (totalByte size f) i := by simp only [u64, read64, u32_bytesOf]

theorem read64_digits (f : Nat → Nat) (pos v : Nat) (bound : v < 2 ^ 64)
    (bytes : ∀ k, k < 8 → f (pos+k) = digit v k) : read64 f pos = v := by
  have h0 := bytes 0 (by decide)
  simp only [Nat.add_zero] at h0
  simp only [read64, read32, read16, Nat.add_assoc, Nat.reduceAdd,
    h0, bytes 1 (by decide), bytes 2 (by decide), bytes 3 (by decide),
    bytes 4 (by decide), bytes 5 (by decide), bytes 6 (by decide), bytes 7 (by decide)]
  simpa only [Nat.add_assoc] using decode8 v bound

def relaByte (rows : List Rela) (i : Nat) : Nat :=
  let r := rows.getD (i/24) ⟨0,0,0⟩
  let j := i%24
  if j < 8 then digit r.offset j else if j < 16 then digit r.info (j-8) else digit r.addend (j-16)

theorem relaByte_offset (rows : List Rela) (n k : Nat) (hk : k < 8) :
    relaByte rows (24*n+k) = digit (rows.getD n ⟨0,0,0⟩).offset k := by
  have q : (24*n+k)/24 = n := by omega
  have r : (24*n+k)%24 = k := by omega
  simp only [relaByte, q, r, if_pos hk]

theorem relaByte_info (rows : List Rela) (n k : Nat) (hk : k < 8) :
    relaByte rows (24*n+8+k) = digit (rows.getD n ⟨0,0,0⟩).info k := by
  have q : (24*n+8+k)/24 = n := by omega
  have r : (24*n+8+k)%24 = 8+k := by omega
  simp only [relaByte, q, r, if_neg (by omega : ¬8+k<8), if_pos (by omega : 8+k<16)]
  congr 1; omega

theorem relaByte_addend (rows : List Rela) (n k : Nat) (hk : k < 8) :
    relaByte rows (24*n+16+k) = digit (rows.getD n ⟨0,0,0⟩).addend k := by
  have q : (24*n+16+k)/24 = n := by omega
  have r : (24*n+16+k)%24 = 16+k := by omega
  simp only [relaByte, q, r, if_neg (by omega : ¬16+k<8), if_neg (by omega : ¬16+k<16)]
  congr 1; omega

def RelaFits (r : Rela) : Prop := r.offset < 2 ^ 64 ∧ r.info < 2 ^ 64 ∧ r.addend < 2 ^ 64
instance (r : Rela) : Decidable (RelaFits r) := by unfold RelaFits; infer_instance

theorem rela_reads (rows : List Rela) (n : Nat) (fit : RelaFits (rows.getD n ⟨0,0,0⟩)) :
    read64 (relaByte rows) (24*n) = (rows.getD n ⟨0,0,0⟩).offset ∧
    read64 (relaByte rows) (24*n+8) = (rows.getD n ⟨0,0,0⟩).info ∧
    read64 (relaByte rows) (24*n+16) = (rows.getD n ⟨0,0,0⟩).addend := by
  refine ⟨read64_digits _ _ _ fit.1 ?_, read64_digits _ _ _ fit.2.1 ?_, read64_digits _ _ _ fit.2.2 ?_⟩
  · intro k hk; exact relaByte_offset rows n k hk
  · intro k hk; exact relaByte_info rows n k hk
  · intro k hk; exact relaByte_addend rows n k hk

theorem read64_congr (f g : Nat → Nat) (a b : Nat)
    (h : ∀ k, k < 8 → f (a+k) = g (b+k)) : read64 f a = read64 g b := by
  have h0 := h 0 (by decide)
  simp only [Nat.add_zero] at h0
  simp only [read64, read32, read16, Nat.add_assoc, Nat.reduceAdd,
    h0, h 1 (by decide), h 2 (by decide), h 3 (by decide),
    h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]

/-- Mapping the row reader over all valid indices reconstructs the original list. -/
theorem rows_reconstruct (rows : List Rela) (read : Nat → Rela)
    (eq : ∀ n, n < rows.length → read n = rows.getD n ⟨0,0,0⟩) :
    (List.range rows.length).map read = rows := by
  apply List.ext_getElem
  · simp
  · intro n hn hn'
    simp only [List.getElem_map, List.getElem_range]
    rw [eq n hn']
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn']

def phF (f : Nat → Nat) : List ProgramHeader :=
  (List.range (read16 f 0x38)).map fun index =>
    let pos := read64 f 0x20 + index * 56
    ⟨read32 f pos, read32 f (pos+4), read64 f (pos+8), read64 f (pos+16), read64 f (pos+32), read64 f (pos+40)⟩

def dynF (phs : List ProgramHeader) (f : Nat → Nat) : List (Nat × Nat) :=
  match phs.find? (·.kind == 2) with
  | none => []
  | some dynamic =>
    ((List.range (dynamic.fileSize/16)).map fun index =>
      (read64 f (dynamic.offset+16 * index), read64 f (dynamic.offset+16 * index+8))).takeWhile (·.1 != 0)

theorem programHeaders_bytesOf (size : Nat) (f : Nat → Nat) :
    programHeaders (bytesOf size f) = phF (totalByte size f) := by
  simp only [programHeaders, phF, u16_bytesOf, u32_bytesOf, u64_bytesOf]

theorem dynamic_of_fields (bytes : Array Nat) (phs : List ProgramHeader) (f : Nat → Nat)
    (ph : programHeaders bytes = phs) (word : ∀ i, u64 bytes i = read64 f i) :
    dynamicEntries bytes = dynF phs f := by
  simp only [dynamicEntries, dynF, ph, word]
  rfl

theorem relaTable_of_fields (bytes : Array Nat) (rows : List Rela) (start total : Nat)
    (v7 : dynamicValue bytes 7 = some start) (v8 : dynamicValue bytes 8 = some total)
    (off : fileOffset bytes start = some start) (len : rows.length = total/24)
    (row : ∀ n, n < rows.length → relaRow bytes start n = rows.getD n ⟨0,0,0⟩) :
    relaTable bytes = some rows := by
  simp only [relaTable, v7, v8, off, Option.map_some]
  have h := rows_reconstruct rows (relaRow bytes start) row
  rw [len] at h
  exact congrArg some h

#print axioms relaTable_of_fields
#print axioms rows_reconstruct
#print axioms rela_reads
#print axioms byte_bytesOf
#print axioms decode8
end SparseELF
