import ArmCertLoop.CopyContext
set_option autoImplicit false

/-! CT1 R-a for route 7: "the 32-bit word at a code VA in a state's memory is w", over loops' route-7 image
    (ContractDraft.image = Image.wordImage imageStart imageWords on codeScope). `WordAt` is literally the same definition
    as CT1.SecpWordCommon.WordAt (that module needs DitShim243, not on the route-7 path). -/

namespace CT1.Route7Word
open ArmCertLoop ArmCertLoop.ContractDraft

/-- The four bytes of word `w` (little-endian) are, in `s`'s memory, at the PAs that `mapping` gives for the VAs
    `imageAddress base (o + i)`, i < 4. (= CT1.SecpWordCommon.WordAt) -/
def WordAt (mapping : BitVec 64 → Option Nat) (s : ArmBridge.Draft.NativeState) (base : BitVec 64) (o w : Nat) : Prop :=
  ∀ i, i < 4 → ∃ pa, mapping (MemReloc.imageAddress base (o + i)) = some pa ∧
    s.mem[pa]? = some (BitVec.extractLsb' (8 * i) 8 (BitVec.ofNat 32 w))

/-- A routine's code: (image offset, word) for `cnt` image words from index `idx0`. -/
def code (idx0 cnt : Nat) : List (Nat × Nat) :=
  (List.range cnt).map fun j =>
    (Generated.imageStart + 4 * (idx0 + j), (Generated.imageWords.getD (idx0 + j) 0).toNat)

/-- Every word of the routine is in `s`'s memory at its image VA. -/
def ImageWords (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (idx0 cnt : Nat)
    (s : ArmBridge.Draft.NativeState) : Prop :=
  ∀ w ∈ code idx0 cnt, WordAt mapping s base w.1 w.2

theorem imageWords_of_placed {mapping : BitVec 64 → Option Nat} {base : BitVec 64} {s : ArmBridge.Draft.NativeState}
    (placed : MemReloc.ImageOn codeScope image s base mapping) (idx0 cnt : Nat)
    (room : idx0 + cnt ≤ Generated.imageWords.length) : ImageWords mapping base idx0 cnt s := by
  intro w hw
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hw
  rw [List.mem_range] at hj
  intro i hi
  obtain ⟨byte, pa, hb, hm, hmem⟩ := placed (Generated.imageStart + 4 * (idx0 + j) + i)
    (by unfold codeScope; constructor <;> omega)
  have hw := Image.image_word Generated.imageStart Generated.imageWords (idx0 + j) (by omega) i hi
  unfold image at hb
  rw [hw] at hb
  cases hb
  refine ⟨pa, hm, ?_⟩
  rw [hmem]
  simp

theorem imageWords_of_mem {mapping : BitVec 64 → Option Nat} {base : BitVec 64} {idx0 cnt : Nat}
    {s t : ArmBridge.Draft.NativeState} (h : t.mem = s.mem) (w : ImageWords mapping base idx0 cnt s) :
    ImageWords mapping base idx0 cnt t := by
  intro c hc i hi
  obtain ⟨pa, hm, hmem⟩ := w c hc i hi
  exact ⟨pa, hm, by rw [h]; exact hmem⟩

theorem mem_code (idx0 cnt j : Nat) (hj : j < cnt) :
    (Generated.imageStart + 4 * (idx0 + j), (Generated.imageWords.getD (idx0 + j) 0).toNat) ∈ code idx0 cnt :=
  List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩

end CT1.Route7Word
#print axioms CT1.Route7Word.imageWords_of_placed
