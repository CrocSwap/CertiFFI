import DitShim243.Deployment
set_option autoImplicit false

/-! CT1 R-a: "the 32-bit word at a code VA in a state's memory is w". Generic over the image/scope of any
    run invariant that carries `MemReloc.ImageOn` (CurrentInv.placed / DefaultMTE2.Core.placed). -/

namespace CT1.SecpWordCommon

/-- The four bytes of word `w` (little-endian) are, in `s`'s memory, at the PAs that `mapping` gives for the VAs
    `imageAddress base (o + i)`, i < 4. -/
def WordAt (mapping : BitVec 64 → Option Nat) (s : ArmBridge.Draft.NativeState) (base : BitVec 64) (o w : Nat) : Prop :=
  ∀ i, i < 4 → ∃ pa, mapping (MemReloc.imageAddress base (o + i)) = some pa ∧
    s.mem[pa]? = some (BitVec.extractLsb' (8 * i) 8 (BitVec.ofNat 32 w))

theorem wordAt_of_placed {scope : Nat → Prop} {image : MemReloc.Image} {s : ArmBridge.Draft.NativeState}
    {base : BitVec 64} {mapping : BitVec 64 → Option Nat} (placed : MemReloc.ImageOn scope image s base mapping)
    (o w : Nat) (inside : ∀ i, i < 4 → scope (o + i))
    (img : ∀ i, i < 4 → image (o + i) = some (BitVec.extractLsb' (8 * i) 8 (BitVec.ofNat 32 w))) :
    WordAt mapping s base o w := by
  intro i hi
  obtain ⟨byte, pa, hb, hm, hmem⟩ := placed (o + i) (inside i hi)
  rw [img i hi] at hb
  cases hb
  exact ⟨pa, hm, hmem⟩

theorem mem_codeOffsets {p : TranslateSpan.SecpRawDeployment.Plan} {c : Nat × Nat} (h : c ∈ p.code) (i : Nat)
    (hi : i < 4) : c.1 + i ∈ TranslateSpan.SecpRawDeployment.codeOffsets p :=
  List.mem_flatMap.mpr ⟨c, h, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩⟩

end CT1.SecpWordCommon
