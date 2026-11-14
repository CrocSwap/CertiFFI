import ReleaseProfile.GB10.HeapWorldData
import TranslateMem.WalkInjSlot
import TranslateMem.RegionsInj

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

/-!
# F21: the replacement premises at the worked Heap world (branch next/f21-no-dbl)

The `card_normalP` card retains NoDoubleMapPA, NoDoubleMapSlot and the caller-buffer layout in place of
DataBytesLinear / RegionsInjective / input-slot separation. Positive C2 discharges them at the world's program data
by finite checks (same pattern as the sealed heap-v2 witness `w_ndPA` / `w_ndSlot` / `w_hd`).
-/

namespace ReleaseProfile.GB10.Heap.F21

open ReleaseProfile.GB10

abbrev P := HeapWorldData.world.pins
abbrev M := HeapWorldData.world.mapping

/-- NoDoubleMapPA as a finite check over the tracked bytes. -/
def ndPAB : Bool :=
  ArmCertValue.HeapV2Mem.heapv2Bytes.all fun a => ArmCertValue.HeapV2Mem.heapv2Bytes.all fun b =>
    match M (ArmCertValue.HeapV2Mem.byteVA P a.1 a.2), M (ArmCertValue.HeapV2Mem.byteVA P b.1 b.2) with
    | some n, some m => !(n / 4096 == m / 4096) ||
        (TranslateMem.pageOf (ArmCertValue.HeapV2Mem.byteVA P a.1 a.2) == TranslateMem.pageOf (ArmCertValue.HeapV2Mem.byteVA P b.1 b.2))
    | _, _ => true

theorem ndPA_check : ndPAB = true := by decide +kernel

theorem ndPA_world : TranslateMem.NoDoubleMapPA P M := by
  intro a ha b hb n m h1 h2 h3
  have := List.all_eq_true.1 (List.all_eq_true.1 ndPA_check a ha) b hb
  simp only [h1, h2, h3, beq_self_eq_true, Bool.not_true, Bool.false_or, beq_iff_eq] at this
  exact this

/-- NoDoubleMapSlot as a finite check over the 32 input-buffer bytes. -/
def ndSlotB : Bool :=
  (List.range 32).all fun j => match M (BitVec.ofNat 64 (P.x1 + j)), M (BitVec.ofNat 64 P.sp) with
    | some q, some n => !(q / 4096 == n / 4096) || ((P.x1 + j) / 4096 == P.sp / 4096)
    | _, _ => true

theorem ndSlot_check : ndSlotB = true := by decide +kernel

theorem ndSlot_world : TranslateMem.NoDoubleMapSlot P M := by
  intro j hj q n h1 h2 h3
  have := List.all_eq_true.1 ndSlot_check j (List.mem_range.2 hj)
  simp only [h1, h2, h3, beq_self_eq_true, Bool.not_true, Bool.false_or, beq_iff_eq] at this
  exact this

theorem layout_world : TranslateMem.RegionsDisjoint P ∧ (P.x1 + 32 ≤ P.sp ∨ P.sp + 16 ≤ P.x1) ∧ P.sp + 16 ≤ 2 ^ 64 :=
  ⟨by unfold TranslateMem.RegionsDisjoint; decide, by decide, by decide⟩

end ReleaseProfile.GB10.Heap.F21

#print axioms ReleaseProfile.GB10.Heap.F21.ndPA_world
#print axioms ReleaseProfile.GB10.Heap.F21.ndSlot_world
#print axioms ReleaseProfile.GB10.Heap.F21.layout_world
