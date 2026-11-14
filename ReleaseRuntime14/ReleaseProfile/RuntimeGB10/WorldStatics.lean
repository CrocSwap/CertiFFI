-- Runtime world code statics and image placement (clean names; ported from R14Init.Placed and PipeR14.SyntheticCS,
-- re-proved over ReleaseProfile.RuntimeGB10.World.mapping/imageRows and WorldPlan.plan by the same kernel sweeps).
import ReleaseProfile.RuntimeGB10.WorldPlan
import PipeR14.FetchR14
set_option autoImplicit false
set_option maxRecDepth 100000
namespace ReleaseProfile.RuntimeGB10.WorldStatics
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ReleaseProfile.RuntimeGB10

def B : BitVec 64 := 0x400000#64

/-- One fetched code word: its 4 bytes are mapped to their code PAs and held by the code plan. -/
def codeWordOK (c : Nat × Nat) : Bool :=
  (List.range 4).all fun i =>
    decide (World.mapping (MemReloc.imageAddress 0x400000#64 (c.1 + i)) =
      some (R14LoaderSynth.codePA (c.1 + i))) &&
    R14LoaderSynth.codePlan.contains (R14LoaderSynth.codePA (c.1 + i), (BitVec.ofNat 32 c.2).extractLsb' (8 * i) 8)

theorem code_words_ok : R14E17.codeVAs.all codeWordOK = true := by decide +kernel

theorem placedAt (db : Nat → BitVec 8) (bytes : Array Nat) (b : StaticPie.Binds bytes R14Scoped.slices)
    (cb : R14E17.CodeBinds bytes) (ifunc : Nat → MemReloc.Word) (x : ArmBridge.Draft.NativeState)
    (hm : NativeSourceInit.Satisfies (WorldPlan.plan db) x.mem) :
    MemReloc.ImageOn PipeR14.closureScope (StaticPie.referenceImageI bytes 0x400000#64 ifunc) x 0x400000#64
      World.mapping := by
  intro o h
  obtain ⟨c, m, i, hi, rfl, himg⟩ := PipeR14.closure_image bytes b cb 0x400000#64 ifunc h
  have ok := List.all_eq_true.1 (List.all_eq_true.1 code_words_ok c m) i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at ok
  refine ⟨_, _, himg, ok.1, hm (R14LoaderSynth.codePA (c.1 + i), (BitVec.ofNat 32 c.2).extractLsb' (8 * i) 8) ?_⟩
  exact List.mem_append_left _ (List.mem_append_left _ ok.2)

/-- World table slots lie in [0x80000000, 0x80005000 - 8]. -/
theorem slots_range : World.imageRows.all (fun r => decide (0x80000000 ≤ r.slot ∧ r.slot + 8 ≤ 0x80005000)) = true := by
  decide +kernel

/-- Code PAs (0x803b6000..) miss the table footprint (0x80000000..0x80005000). -/
theorem separatedAt : ImageTableSeparated PipeR14.closureScope 0x400000#64 World.mapping
    (rowsFootprint World.imageRows).byte := by
  intro offset pa inside hmap ⟨slot, hs, lo, hi⟩
  obtain ⟨c, m, i, hi4, rfl⟩ := inside
  have ok := List.all_eq_true.1 (List.all_eq_true.1 code_words_ok c m) i (List.mem_range.2 hi4)
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at ok
  rw [ok.1] at hmap
  cases hmap
  have hr := of_decide_eq_true (List.all_eq_true.1 R14LoaderSynth.codePlan_range _ ok.2)
  simp only [rowsFootprint, List.mem_map] at hs
  obtain ⟨row, rm, rfl⟩ := hs
  have hs := of_decide_eq_true (List.all_eq_true.1 slots_range row rm)
  have hw : (rowsFootprint World.imageRows).width = 8 := rfl
  simp only at hr
  omega

/-- One code word: mapped, its 4 bytes contiguous, and its PA (a 56-bit address) outside the MMIO pages. -/
def wordOK (c : Nat × Nat) : Bool :=
  match World.mapping (MemReloc.imageAddress B c.1) with
  | none => false
  | some pa =>
    (List.range 4).all (fun i => World.mapping (MemReloc.imageAddress B (c.1 + i)) == some (pa + i)) &&
    decide (pa < 2 ^ 56) && decide (Sail.BitVec.extractLsb (BitVec.ofNat 56 pa) 55 16 ≠ 0x2C00#40) &&
    decide (Sail.BitVec.extractLsb (BitVec.ofNat 56 pa) 55 16 ≠ 0x3C00#40)

theorem words_ok : R14E17.codeVAs.all wordOK = true := by decide +kernel

theorem contiguous : ∀ c ∈ R14E17.codeVAs, ImageWordContiguous World.mapping B c.1 := by
  intro c m i hi pa hpa
  have ok := List.all_eq_true.1 words_ok c m
  unfold wordOK at ok
  rw [hpa] at ok
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at ok
  exact ok.1.1.1 i hi

theorem notMMIO : ∀ c ∈ R14E17.codeVAs, MappedNotMMIO World.mapping (MemReloc.imageAddress B c.1) := by
  intro c m pa hpa
  have ok := List.all_eq_true.1 words_ok c m
  unfold wordOK at ok
  rw [hpa] at ok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ok
  have e : pa = BitVec.ofNat 56 pa.toNat := by simp
  rw [e]; exact ⟨ok.1.2, ok.2⟩

/-- The world's code statics. -/
theorem cs : PipeR14.CodeStaticR14 PipeR14.closureScope World.mapping B (rowsFootprint World.imageRows).byte where
  covers := PipeR14.closure_covers
  separated := separatedAt
  contiguous := contiguous
  notMMIO := notMMIO

#print axioms placedAt
#print axioms cs
end ReleaseProfile.RuntimeGB10.WorldStatics
