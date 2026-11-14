import R14E17.Fetch

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

/-!
# Runtime reviewed image bytes (seal: Lean image data <-> ELF link)

`reviewedImageBytes` lists `(link vaddr, byte)`, at load base 0, for every ELF file byte that the Runtime card statements
constrain beyond the slices. Those are the little-endian bytes of the 14 cases' plan code words, `R14E17.codeVAs`,
which is the data `R14E17.CodeBinds` uses. They all lie in the RX PT_LOAD, where file offset = vaddr − 0x10000.
`codeBinds_iff` shows `CodeBinds bytes` holds exactly when the file `bytes` agree with the table.

The statements' other premise on the file, `StaticPie.Binds bytes R14Scoped.slices` (size, ELF header, program headers,
dynamic, RELA rows), is bound to the ELF by the sha-pinned slice generator (R14Scoped.Instance header: square.elf
55b0e3bf...). No other PT_LOAD byte is constrained: the statements hold for every file satisfying both premises.
-/

namespace ReleaseProfile.GB10.RuntimeImage

open ArmCert.Translate.Model.StaticPie

/-- `(link vaddr, byte)` for every code byte the Runtime statements constrain (CodeBinds), load base 0. -/
def reviewedImageBytes : Array (Nat × Nat) :=
  (R14E17.codeVAs.flatMap fun c => (List.range 4).map fun i => (c.1 + i, (c.2 >>> (8 * i)) % 256)).toArray

/-- The RX PT_LOAD file-offset map used by `CodeBinds`. -/
def fileOffset (vaddr : Nat) : Nat := vaddr - 0x10000

theorem codeVAs_ge (c : Nat × Nat) (h : c ∈ R14E17.codeVAs) : 0x10000 ≤ c.1 := by
  have := List.all_eq_true.1 R14E17.codeVAs_ok c h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  have : R14E17.rxLo ≤ c.1 := this.1.1
  unfold R14E17.rxLo at this
  omega

/-- `CodeBinds` is exactly agreement of the file bytes with the table at the RX file offsets. -/
theorem codeBinds_iff (bytes : Array Nat) :
    R14E17.CodeBinds bytes ↔ ∀ ab ∈ reviewedImageBytes.toList, byte bytes (fileOffset ab.1) = ab.2 := by
  unfold R14E17.CodeBinds reviewedImageBytes fileOffset
  simp only [List.toList_toArray, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro h _ ⟨c, hc, i, hi, rfl⟩
    have := codeVAs_ge c hc
    rw [show c.1 + i - 0x10000 = c.1 - 0x10000 + i by omega]
    exact h c hc i hi
  · intro h c hc i hi
    have := codeVAs_ge c hc
    have := h _ ⟨c, hc, i, hi, rfl⟩
    rwa [show c.1 + i - 0x10000 = c.1 - 0x10000 + i by omega] at this

end ReleaseProfile.GB10.RuntimeImage

#eval ReleaseProfile.GB10.RuntimeImage.reviewedImageBytes.size
#print axioms ReleaseProfile.GB10.RuntimeImage.codeBinds_iff
