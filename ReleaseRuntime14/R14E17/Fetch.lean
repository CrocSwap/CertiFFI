import R14E17.Table
import R14Scoped.Instance

/-! runtime14 E17 obligation (1b), fetch side: at every plan code word of the 14 cases, the actual
loader image (`referenceImageI`, any load base, any IRELATIVE resolver results) holds that word's little-endian
bytes. From: the d188 scoped admission (`runtime14_scoped`), no RELA slot touching the RX segment (decided per
chunk), the RX PT_LOAD mapping image offset x to file offset x − 0x10000, and `CodeBinds` — the plan's code words
are the file's bytes, which the sha-pinned plan generator establishes (it reads the words from the ELF), as
`Binds` does for the slices. The generic C9 lemmas (`c9_fetch_code`, `mapped_bytes_present_of_image_on`) take
this image fact per word, as in HeapV2Fetch. -/

open ArmCert.Translate.Model.StaticPie
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace R14E17

/-- The RX PT_LOAD: image [0x2b6300, 0xa025b0), file offset = image offset − 0x10000. -/
def rxLo : Nat := 0x2b6300
def rxHi : Nat := 0xa025b0

/-- The code words of all 14 cases as (image offset, word). -/
def codeVAs : List (Nat × Nat) :=
  (List.range 14).flatMap fun n => match caseMap n with
    | some (_, cws, e) => cws.map fun c => (e + c.1, c.2)
    | none => []

/-- The plan's code words are the file's bytes (established by the sha-pinned plan generator). -/
def CodeBinds (bytes : Array Nat) : Prop :=
  ∀ c ∈ codeVAs, ∀ i < 4, byte bytes (c.1 - 0x10000 + i) = (c.2 >>> (8 * i)) % 256

theorem codeVAs_ok : codeVAs.all (fun c => decide (rxLo ≤ c.1 ∧ c.1 + 4 ≤ rxHi ∧ c.2 < 2 ^ 32) &&
    (List.range 4).all fun i => inRanges R14Scoped.closure.code (c.1 + i)) = true := by decide +kernel

def rxClear (r : Rela) : Bool := decide (rxHi ≤ r.offset) || decide (r.offset + 8 ≤ rxLo)

theorem chunk00_rx : R14Scoped.chunk00.all rxClear = true := by decide +kernel
theorem chunk01_rx : R14Scoped.chunk01.all rxClear = true := by decide +kernel
theorem chunk02_rx : R14Scoped.chunk02.all rxClear = true := by decide +kernel
theorem chunk03_rx : R14Scoped.chunk03.all rxClear = true := by decide +kernel
theorem chunk04_rx : R14Scoped.chunk04.all rxClear = true := by decide +kernel
theorem chunk05_rx : R14Scoped.chunk05.all rxClear = true := by decide +kernel
theorem chunk06_rx : R14Scoped.chunk06.all rxClear = true := by decide +kernel
theorem chunk07_rx : R14Scoped.chunk07.all rxClear = true := by decide +kernel
theorem chunk08_rx : R14Scoped.chunk08.all rxClear = true := by decide +kernel
theorem chunk09_rx : R14Scoped.chunk09.all rxClear = true := by decide +kernel
theorem chunk10_rx : R14Scoped.chunk10.all rxClear = true := by decide +kernel
theorem chunk11_rx : R14Scoped.chunk11.all rxClear = true := by decide +kernel
theorem chunk12_rx : R14Scoped.chunk12.all rxClear = true := by decide +kernel
theorem chunk13_rx : R14Scoped.chunk13.all rxClear = true := by decide +kernel
theorem chunk14_rx : R14Scoped.chunk14.all rxClear = true := by decide +kernel
theorem chunk15_rx : R14Scoped.chunk15.all rxClear = true := by decide +kernel
theorem chunk16_rx : R14Scoped.chunk16.all rxClear = true := by decide +kernel
theorem chunk17_rx : R14Scoped.chunk17.all rxClear = true := by decide +kernel
theorem chunk18_rx : R14Scoped.chunk18.all rxClear = true := by decide +kernel
theorem chunk19_rx : R14Scoped.chunk19.all rxClear = true := by decide +kernel
theorem chunk20_rx : R14Scoped.chunk20.all rxClear = true := by decide +kernel
theorem chunk21_rx : R14Scoped.chunk21.all rxClear = true := by decide +kernel
theorem chunk22_rx : R14Scoped.chunk22.all rxClear = true := by decide +kernel
theorem chunk23_rx : R14Scoped.chunk23.all rxClear = true := by decide +kernel
theorem chunk24_rx : R14Scoped.chunk24.all rxClear = true := by decide +kernel
theorem chunk25_rx : R14Scoped.chunk25.all rxClear = true := by decide +kernel
theorem chunk26_rx : R14Scoped.chunk26.all rxClear = true := by decide +kernel
theorem chunk27_rx : R14Scoped.chunk27.all rxClear = true := by decide +kernel
theorem chunk28_rx : R14Scoped.chunk28.all rxClear = true := by decide +kernel
theorem chunk29_rx : R14Scoped.chunk29.all rxClear = true := by decide +kernel
theorem chunk30_rx : R14Scoped.chunk30.all rxClear = true := by decide +kernel

theorem rela_rx : R14Scoped.slices.rela.all rxClear = true := by
  simp only [R14Scoped.slices, List.all_append, chunk00_rx, chunk01_rx, chunk02_rx, chunk03_rx, chunk04_rx, chunk05_rx, chunk06_rx, chunk07_rx, chunk08_rx, chunk09_rx, chunk10_rx, chunk11_rx, chunk12_rx, chunk13_rx, chunk14_rx, chunk15_rx, chunk16_rx, chunk17_rx, chunk18_rx, chunk19_rx, chunk20_rx, chunk21_rx, chunk22_rx, chunk23_rx, chunk24_rx, chunk25_rx, chunk26_rx, chunk27_rx, chunk28_rx, chunk29_rx, chunk30_rx, Bool.and_self]

theorem segments_eq (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) :
    (loads bytes).map normalize =
      [⟨0x0, 0x0, 0x2a62f8, 0x2a62f8⟩, ⟨0x2a6300, 0x2b6300, 0x74c2b0, 0x74c2b0⟩,
        ⟨0x9f25b0, 0xa125b0, 0x73298, 0x73a50⟩, ⟨0xa65880, 0xa95880, 0xc100, 0x3e1b1⟩] := by
  rw [loads_of_binds b]; rfl

theorem word_byte (w i : Nat) (hw : w < 2 ^ 32) (hi : i < 4) :
    BitVec.ofNat 8 ((w >>> (8 * i)) % 256) = (BitVec.ofNat 32 w).extractLsb' (8 * i) 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.mod_eq_of_lt hw, Nat.reducePow, Nat.mod_mod]

set_option maxRecDepth 100000 in
/-- The loader image at a plan code word byte is that byte of the word. -/
theorem code_image (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : CodeBinds bytes)
    (base : MemReloc.Word) (ifunc : Nat → MemReloc.Word) {c : Nat × Nat} (member : c ∈ codeVAs)
    (i : Nat) (hi : i < 4) :
    referenceImageI bytes base ifunc (c.1 + i) = some ((BitVec.ofNat 32 c.2).extractLsb' (8 * i) 8) := by
  have ok := List.all_eq_true.1 codeVAs_ok c member
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at ok
  obtain ⟨⟨lo, hi4, hw⟩, cov⟩ := ok
  have adm := R14Scoped.runtime14_scoped bytes b
  rw [adm.image base ifunc _ (Or.inl (cov i hi))]
  rw [MemReloc.relocatedImage_unpatched]
  · rw [segments_eq bytes b]
    have hsize : bytes.size = 17533320 := b.size
    simp only [MemReloc.loadSegments, List.foldl_cons, List.foldl_nil, MemReloc.loadSegment]
    have h1 : ¬ (0x0 ≤ c.1 + i ∧ c.1 + i < 0x0 + 0x2a62f8) := by simp only [rxLo] at lo; omega
    have h2 : 0x2b6300 ≤ c.1 + i ∧ c.1 + i < 0x2b6300 + 0x74c2b0 := by simp only [rxLo, rxHi] at lo hi4; omega
    have h3 : c.1 + i - 0x2b6300 < 0x74c2b0 := by simp only [rxHi] at hi4; omega
    have h4 : ¬ (0xa125b0 ≤ c.1 + i ∧ c.1 + i < 0xa125b0 + 0x73a50) := by simp only [rxHi] at hi4; omega
    have h5 : ¬ (0xa95880 ≤ c.1 + i ∧ c.1 + i < 0xa95880 + 0x3e1b1) := by simp only [rxHi] at hi4; omega
    simp only [h1, h2, h3, h4, h5, ite_true, ite_false, fileImage]
    have off : 0x2a6300 + (c.1 + i - 0x2b6300) = c.1 - 0x10000 + i := by simp only [rxLo] at lo; omega
    have inb : c.1 - 0x10000 + i < bytes.size := by simp only [rxHi] at hi4; omega
    rw [off, Array.getElem?_eq_getElem inb, Option.map_some, ← word_byte c.2 i hw hi, ← cb c member i hi]
    simp [byte, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inb]
  · intro patch m
    simp only [relativePatchesOf, List.mem_map, List.mem_filter] at m
    obtain ⟨r, ⟨rm, _⟩, rfl⟩ := m
    have h := List.all_eq_true.1 rela_rx r rm
    have h' : rxHi ≤ r.offset ∨ r.offset + 8 ≤ rxLo := by simpa [rxClear] using h
    simp only [rxLo, rxHi] at h' lo hi4
    simp only [Rela.patch]
    omega

theorem mem_codeVAs {n : Nat} {accs : List Access} {cws : List (Nat × Nat)} {entry : Nat}
    (hn : n < 14) (h : caseMap n = some (accs, cws, entry)) {c : Nat × Nat} (m : c ∈ cws) :
    (entry + c.1, c.2) ∈ codeVAs := by
  simp only [codeVAs, List.mem_flatMap, List.mem_range]
  exact ⟨n, hn, by rw [h]; exact List.mem_map.2 ⟨c, m, rfl⟩⟩

/-- Per case: the image bytes at every plan code word (the `imageWord` premise of `c9_fetch_code`). -/
theorem case_code_image (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : CodeBinds bytes)
    (base : MemReloc.Word) (ifunc : Nat → MemReloc.Word) {n : Nat} {accs : List Access}
    {cws : List (Nat × Nat)} {entry : Nat} (hn : n < 14) (h : caseMap n = some (accs, cws, entry))
    {c : Nat × Nat} (m : c ∈ cws) :
    ∀ i < 4, referenceImageI bytes base ifunc (entry + c.1 + i) = some ((BitVec.ofNat 32 c.2).extractLsb' (8 * i) 8) :=
  fun i hi => code_image bytes b cb base ifunc (mem_codeVAs hn h m) i hi

#print axioms rela_rx
#print axioms code_image
#print axioms case_code_image
end R14E17
