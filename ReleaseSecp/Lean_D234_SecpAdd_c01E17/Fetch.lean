import Lean_D234_SecpAdd_c01E17.Table
import Lean_D234_SecpAdd_c01Scoped.Instance

/-! PipeLean_D234_SecpAdd_c01 E17 obligation (1b), fetch side: at every plan code word of the 1 cases, the actual
loader image (`referenceImageI`, any load base, any IRELATIVE resolver results) holds that word's little-endian
bytes. From: the d188 scoped admission (`PipeLean_D234_SecpAdd_c01_scoped`), no RELA slot touching the RX segment (decided per
chunk), the RX PT_LOAD mapping image offset x to file offset 0x638 + (x − 0x1638), and `CodeBinds` — the plan's code words
are the file's bytes, which the sha-pinned plan generator establishes (it reads the words from the ELF), as
`Binds` does for the slices. The generic C9 lemmas (`c9_fetch_code`, `mapped_bytes_present_of_image_on`) take
this image fact per word, as in HeapV2Fetch. -/

open ArmCert.Translate.Model.StaticPie
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Lean_D234_SecpAdd_c01E17

/-- The RX PT_LOAD: image [0x1638, 0x2154), file offset = 0x638 + (image offset − 0x1638). -/
def rxLo : Nat := 0x1638
def rxHi : Nat := 0x2154

/-- The code words of all 1 cases as (image offset, word). -/
def codeVAs : List (Nat × Nat) :=
  (List.range 1).flatMap fun n => match caseMap n with
    | some (_, cws, e) => cws.map fun c => (e + c.1, c.2)
    | none => []

/-- The plan's code words are the file's bytes (established by the sha-pinned plan generator). -/
def CodeBinds (bytes : Array Nat) : Prop :=
  ∀ c ∈ codeVAs, ∀ i < 4, byte bytes ((1592 + (c.1 - 5688) + i)) = (c.2 >>> (8 * i)) % 256

theorem codeVAs_ok : codeVAs.all (fun c => decide (rxLo ≤ c.1 ∧ c.1 + 4 ≤ rxHi ∧ c.2 < 2 ^ 32) &&
    (List.range 4).all fun i => inRanges Lean_D234_SecpAdd_c01Scoped.closure.code (c.1 + i)) = true := by decide +kernel

def rxClear (r : Rela) : Bool := decide (rxHi ≤ r.offset) || decide (r.offset + 8 ≤ rxLo)

theorem rela_rx : Lean_D234_SecpAdd_c01Scoped.slices.rela.all rxClear = true := by
  rfl
theorem segments_eq (bytes : Array Nat) (b : Binds bytes Lean_D234_SecpAdd_c01Scoped.slices) :
    (loads bytes).map normalize = [⟨0, 0, 1592, 1592⟩, ⟨1592, 5688, 2844, 2844⟩, ⟨4440, 12632, 176, 3752⟩] := by
  rw [loads_of_binds b]; rfl

theorem word_byte (w i : Nat) (hw : w < 2 ^ 32) (hi : i < 4) :
    BitVec.ofNat 8 ((w >>> (8 * i)) % 256) = (BitVec.ofNat 32 w).extractLsb' (8 * i) 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.mod_eq_of_lt hw, Nat.reducePow, Nat.mod_mod]

set_option maxRecDepth 100000 in
/-- The loader image at a plan code word byte is that byte of the word. -/
theorem code_image (bytes : Array Nat) (b : Binds bytes Lean_D234_SecpAdd_c01Scoped.slices) (cb : CodeBinds bytes)
    (base : MemReloc.Word) (ifunc : Nat → MemReloc.Word) {c : Nat × Nat} (member : c ∈ codeVAs)
    (i : Nat) (hi : i < 4) :
    referenceImageI bytes base ifunc (c.1 + i) = some ((BitVec.ofNat 32 c.2).extractLsb' (8 * i) 8) := by
  have ok := List.all_eq_true.1 codeVAs_ok c member
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at ok
  obtain ⟨⟨lo, hi4, hw⟩, cov⟩ := ok
  have adm := Lean_D234_SecpAdd_c01Scoped.lean_d234_secpadd_c01_scoped bytes b
  rw [adm.image base ifunc _ (Or.inl (cov i hi))]
  rw [MemReloc.relocatedImage_unpatched]
  · rw [segments_eq bytes b]
    have hsize : bytes.size = 8048 := b.size
    simp only [MemReloc.loadSegments, List.foldl_cons, List.foldl_nil, MemReloc.loadSegment]
    have hs0 : ¬ (0 ≤ c.1 + i ∧ c.1 + i < 0 + 1592) := by simp only [rxLo, rxHi] at lo hi4; omega
    have hs1 : 5688 ≤ c.1 + i ∧ c.1 + i < 5688 + 2844 := by simp only [rxLo, rxHi] at lo hi4; omega
    have hf1 : c.1 + i - 5688 < 2844 := by simp only [rxLo, rxHi] at lo hi4; omega
    have hs2 : ¬ (12632 ≤ c.1 + i ∧ c.1 + i < 12632 + 3752) := by simp only [rxLo, rxHi] at lo hi4; omega
    simp only [hs0, hs1, hf1, hs2, ite_true, ite_false, fileImage]
    have off : 1592 + (c.1 + i - 5688) = (1592 + (c.1 - 5688) + i) := by simp only [rxLo] at lo; omega
    have inb : (1592 + (c.1 - 5688) + i) < bytes.size := by simp only [rxLo, rxHi] at lo hi4; omega
    rw [off, Array.getElem?_eq_getElem inb, Option.map_some, ← word_byte c.2 i hw hi, ← cb c member i hi]
    simpa [byte, Array.getD_eq_getD_getElem?] using
      (congrArg (fun x : Option Nat => some (BitVec.ofNat 8 (x.getD 0))) (Array.getElem?_eq_getElem inb)).symm
  · intro patch m
    simp only [relativePatchesOf, List.mem_map, List.mem_filter] at m
    obtain ⟨r, ⟨rm, _⟩, rfl⟩ := m
    have h := List.all_eq_true.1 rela_rx r rm
    have h' : rxHi ≤ r.offset ∨ r.offset + 8 ≤ rxLo := by simpa [rxClear] using h
    simp only [rxLo, rxHi] at h' lo hi4
    simp only [Rela.patch]
    omega

theorem mem_codeVAs {n : Nat} {accs : List Access} {cws : List (Nat × Nat)} {entry : Nat}
    (hn : n < 1) (h : caseMap n = some (accs, cws, entry)) {c : Nat × Nat} (m : c ∈ cws) :
    (entry + c.1, c.2) ∈ codeVAs := by
  simp only [codeVAs, List.mem_flatMap, List.mem_range]
  exact ⟨n, hn, by rw [h]; exact List.mem_map.2 ⟨c, m, rfl⟩⟩

/-- Per case: the image bytes at every plan code word (the `imageWord` premise of `c9_fetch_code`). -/
theorem case_code_image (bytes : Array Nat) (b : Binds bytes Lean_D234_SecpAdd_c01Scoped.slices) (cb : CodeBinds bytes)
    (base : MemReloc.Word) (ifunc : Nat → MemReloc.Word) {n : Nat} {accs : List Access}
    {cws : List (Nat × Nat)} {entry : Nat} (hn : n < 1) (h : caseMap n = some (accs, cws, entry))
    {c : Nat × Nat} (m : c ∈ cws) :
    ∀ i < 4, referenceImageI bytes base ifunc (entry + c.1 + i) = some ((BitVec.ofNat 32 c.2).extractLsb' (8 * i) 8) :=
  fun i hi => code_image bytes b cb base ifunc (mem_codeVAs hn h m) i hi

#print axioms rela_rx
#print axioms code_image
#print axioms case_code_image
end Lean_D234_SecpAdd_c01E17
