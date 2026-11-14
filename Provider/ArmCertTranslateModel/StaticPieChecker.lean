import ArmCertTranslateModel.HeapV2Image

/-! Decision-136 loader checker: a fail-closed parse of raw ELF64 bytes for the
admitted static-PIE form. It returns the normalized C9 segments (PT_LOAD in header
order) and RELATIVE patches only when the file is a little-endian AArch64 ET_DYN
with the PIE flag, every program header and PT_LOAD lies inside the file, and the
only dynamic relocations (if any) are RELA entries of type R_AARCH64_RELATIVE.
REL/RELR/JMPREL/TEXTREL tables and any other RELA type (IRELATIVE included) are
rejected. No OS loader or self-relocator correctness is claimed. -/

set_option autoImplicit false
set_option maxRecDepth 100000
namespace ArmCert.Translate.Model.StaticPie

def byte (bytes : Array Nat) (index : Nat) : Nat := bytes.getD index 0
def u16 (bytes : Array Nat) (index : Nat) : Nat := byte bytes index + 256 * byte bytes (index + 1)
def u32 (bytes : Array Nat) (index : Nat) : Nat := u16 bytes index + 65536 * u16 bytes (index + 2)
def u64 (bytes : Array Nat) (index : Nat) : Nat := u32 bytes index + 4294967296 * u32 bytes (index + 4)

structure ProgramHeader where
  kind : Nat
  flags : Nat
  offset : Nat
  vaddr : Nat
  fileSize : Nat
  memorySize : Nat
  deriving DecidableEq, Repr

def programHeaders (bytes : Array Nat) : List ProgramHeader :=
  (List.range (u16 bytes 0x38)).map fun index =>
    let pos := u64 bytes 0x20 + index * 56
    ⟨u32 bytes pos, u32 bytes (pos + 4), u64 bytes (pos + 8), u64 bytes (pos + 16), u64 bytes (pos + 32),
      u64 bytes (pos + 40)⟩

def headerOK (bytes : Array Nat) : Bool :=
  decide (64 ≤ bytes.size) && byte bytes 0 == 0x7f && byte bytes 1 == 0x45 && byte bytes 2 == 0x4c &&
  byte bytes 3 == 0x46 && byte bytes 4 == 2 && byte bytes 5 == 1 && u16 bytes 0x10 == 3 &&
  u16 bytes 0x12 == 0xb7 && u16 bytes 0x36 == 56 &&
  decide (u64 bytes 0x20 + u16 bytes 0x38 * 56 ≤ bytes.size)

def loads (bytes : Array Nat) : List ProgramHeader := (programHeaders bytes).filter (·.kind == 1)

def loadsOK (bytes : Array Nat) : Bool :=
  (loads bytes).all fun header =>
    decide (header.offset + header.fileSize ≤ bytes.size) && decide (header.fileSize ≤ header.memorySize)

/-- Dynamic entries (tag, value) up to, excluding, DT_NULL. -/
def dynamicEntries (bytes : Array Nat) : List (Nat × Nat) :=
  match (programHeaders bytes).find? (·.kind == 2) with
  | none => []
  | some dynamic =>
    ((List.range (dynamic.fileSize / 16)).map fun index =>
      (u64 bytes (dynamic.offset + 16 * index), u64 bytes (dynamic.offset + 16 * index + 8))).takeWhile
      (·.1 != 0)

def dynamicValue (bytes : Array Nat) (tag : Nat) : Option Nat :=
  ((dynamicEntries bytes).find? (·.1 == tag)).map (·.2)

/-- DT_FLAGS_1 carries DF_1_PIE. -/
def pieFlag (bytes : Array Nat) : Bool :=
  match dynamicValue bytes 0x6ffffffb with
  | some flags => (flags / 0x8000000) % 2 == 1
  | none => false

/-- File offset of a virtual address inside some PT_LOAD's file bytes. -/
def fileOffset (bytes : Array Nat) (vaddr : Nat) : Option Nat :=
  ((loads bytes).find? fun header => decide (header.vaddr ≤ vaddr ∧ vaddr < header.vaddr + header.fileSize)).map
    fun header => header.offset + (vaddr - header.vaddr)

/-- RELA entries as RELATIVE patches, failing closed on any other type. -/
def relativePatches (bytes : Array Nat) : Option (List MemReloc.RelativePatch) :=
  if [17, 22, 23, 36].any (fun tag => (dynamicValue bytes tag).isSome) then none else
  match dynamicValue bytes 7, dynamicValue bytes 8 with
  | none, none => some []
  | some address, some total =>
    match fileOffset bytes address with
    | none => none
    | some start =>
      ((List.range (total / 24)).map fun index =>
        let pos := start + 24 * index
        (u64 bytes pos, u64 bytes (pos + 8) % 4294967296, u64 bytes (pos + 16))).foldr
        (fun (entry : Nat × Nat × Nat) rest =>
          if entry.2.1 == 1027 then rest.map (⟨entry.1, BitVec.ofNat 64 entry.2.2⟩ :: ·) else none)
        (some [])
  | _, _ => none

/-- The decision-136 checker: normalized segments and RELATIVE patches, or `none`. -/
def check (bytes : Array Nat) : Option (List MemReloc.LoadSegment × List MemReloc.RelativePatch) :=
  if headerOK bytes && loadsOK bytes && pieFlag bytes then
    (relativePatches bytes).map fun patches =>
      ((loads bytes).map fun header => ⟨header.offset, header.vaddr, header.fileSize, header.memorySize⟩,
        patches)
  else none

set_option maxHeartbeats 400000 in
/-- heap-v2: the checker accepts the raw ELF bytes and yields exactly the normalized
    segments and (empty) patches that the C9 image is built from. -/
theorem heapv2_check : check HeapV2.fileBytes = some (HeapV2.segments, HeapV2.patches) := by
  rfl

#print axioms heapv2_check
end ArmCert.Translate.Model.StaticPie
