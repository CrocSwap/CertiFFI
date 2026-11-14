import PipeLean_D234_SecpNeg_c10.ImageBinding
import DitShim243.InitialCheck
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-!
# secp shim words: the loader image on the RX segment of SecpArtifact.elf (card-independent)

`referenceImageI` at any image offset of the RX PT_LOAD ([0x1638, 0x2154)) is the file byte at 0x638 + (x − 0x1638).
Same argument as the per-card E17 `code_image`, but the IRELATIVE clearance comes from `rela_rx` (no RELA slot touches
the RX segment) instead of the card's scoped closure, so it covers the DIT shim stubs (outside every card closure).
The ELF facts (Binds, scoped admission frame, RELA table, segments) are the c10 E17/ImageBinding ones: one ELF.
-/

open ArmCert.Translate.Model.StaticPie

namespace ReleaseProfile.GB10.SecpShimRuntime.ShimImage

theorem rx_image (base : MemReloc.Word) (ifunc : Nat → MemReloc.Word) (x : Nat)
    (lo : 5688 ≤ x) (hi : x < 8532) :
    referenceImageI SecpArtifact.elf base ifunc x = some (BitVec.ofNat 8 (byte SecpArtifact.elf (1592 + (x - 5688)))) := by
  have b := PipeLean_D234_SecpNeg_c10.ImageBinding.image_binds
  have adm := PipeLean_D234_SecpNeg_c10.ImageBinding.scoped_image
  have img : referenceImageI SecpArtifact.elf base ifunc x =
      MemReloc.relocatedImage (fileImage SecpArtifact.elf) ((loads SecpArtifact.elf).map normalize)
        (relativePatchesOf Lean_D234_SecpNeg_c10Scoped.slices.rela) base x := by
    simp only [referenceImageI, b.rela, Option.getD_some, MemReloc.relocatedImage, MemReloc.loadSegments,
      relativePatchesOf]
    rw [loads_eq SecpArtifact.elf _ _ (fun header member => (adm.loadsInFile header member).1), ← relocs_eq]
    apply fold_scoped base ifunc x _ _ _ rfl
    intro r member
    rcases adm.relaScoped r member with rel | ⟨irel, _, _⟩
    · exact Or.inl rel
    · refine Or.inr ⟨irel, ?_⟩
      have h := List.all_eq_true.1 Lean_D234_SecpNeg_c10E17.rela_rx r member
      have h' : Lean_D234_SecpNeg_c10E17.rxHi ≤ r.offset ∨ r.offset + 8 ≤ Lean_D234_SecpNeg_c10E17.rxLo := by
        simpa [Lean_D234_SecpNeg_c10E17.rxClear] using h
      simp only [Lean_D234_SecpNeg_c10E17.rxLo, Lean_D234_SecpNeg_c10E17.rxHi] at h'
      omega
  rw [img, MemReloc.relocatedImage_unpatched]
  · rw [Lean_D234_SecpNeg_c10E17.segments_eq SecpArtifact.elf b]
    have hsize : SecpArtifact.elf.size = 8048 := b.size
    simp only [MemReloc.loadSegments, List.foldl_cons, List.foldl_nil, MemReloc.loadSegment]
    have hs0 : ¬ (0 ≤ x ∧ x < 0 + 1592) := by omega
    have hs1 : 5688 ≤ x ∧ x < 5688 + 2844 := by omega
    have hf1 : x - 5688 < 2844 := by omega
    have hs2 : ¬ (12632 ≤ x ∧ x < 12632 + 3752) := by omega
    simp only [hs0, hs1, hf1, hs2, ite_true, ite_false, fileImage]
    have inb : 1592 + (x - 5688) < SecpArtifact.elf.size := by omega
    rw [Array.getElem?_eq_getElem inb, Option.map_some]
    simp [byte, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inb]
  · intro patch m
    simp only [relativePatchesOf, List.mem_map, List.mem_filter] at m
    obtain ⟨r, ⟨rm, _⟩, rfl⟩ := m
    have h := List.all_eq_true.1 Lean_D234_SecpNeg_c10E17.rela_rx r rm
    have h' : Lean_D234_SecpNeg_c10E17.rxHi ≤ r.offset ∨ r.offset + 8 ≤ Lean_D234_SecpNeg_c10E17.rxLo := by
      simpa [Lean_D234_SecpNeg_c10E17.rxClear] using h
    simp only [Lean_D234_SecpNeg_c10E17.rxLo, Lean_D234_SecpNeg_c10E17.rxHi] at h'
    simp only [Rela.patch]
    omega

/-- The closed per-card file check for the 11 shim words at `start`. -/
def wordsFile (start : Nat) (imm : BitVec 26) : Bool :=
  (List.range 11).all fun j => (List.range 4).all fun i =>
    some (BitVec.ofNat 8 (byte SecpArtifact.elf (1592 + (start + 4 * j + i - 5688)))) ==
      some ((DitShim243.Fetches.word imm j).extractLsb' (8 * i) 8)

theorem checkWords_of_file (base : MemReloc.Word) (ifunc : Nat → MemReloc.Word) (start : Nat) (imm : BitVec 26)
    (lo : 5688 ≤ start) (hi : start + 44 ≤ 8532) (h : wordsFile start imm = true) :
    DitShim243.InitialCheck.checkWords (referenceImageI SecpArtifact.elf base ifunc) start imm = true := by
  unfold DitShim243.InitialCheck.checkWords
  apply List.all_eq_true.2; intro j hj; apply List.all_eq_true.2; intro i hi'
  have hj' := List.mem_range.1 hj; have hi'' := List.mem_range.1 hi'
  rw [rx_image base ifunc _ (by omega) (by omega)]
  exact List.all_eq_true.1 (List.all_eq_true.1 h j hj) i hi'

end ReleaseProfile.GB10.SecpShimRuntime.ShimImage

#print axioms ReleaseProfile.GB10.SecpShimRuntime.ShimImage.rx_image
#print axioms ReleaseProfile.GB10.SecpShimRuntime.ShimImage.checkWords_of_file

