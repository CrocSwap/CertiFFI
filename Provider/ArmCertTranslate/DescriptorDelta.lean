import Init

/-! Exact raw-bit restriction for a classic 64-bit descriptor update. This is a
relation on descriptor words, not a walker or an assumed execution result. The
model adapter must prove that actual hardware writes satisfy it. -/
namespace ArmCert.Translate

/-- The only mutable bits are AF (10) and dirty state (7). AF only goes 0→1;
    dirty state only goes 1→0 and requires HA, HD and DBM in the legacy regime.
    PIE's dirty authorization is separate from legacy DBM. -/
structure DescriptorDelta (ha hd pie : Bool) (before after : BitVec 64) : Prop where
  fixed : ∀ i, i < 64 → i ≠ 7 → i ≠ 10 → after.getLsbD i = before.getLsbD i
  af_mono : before.getLsbD 10 = true → after.getLsbD 10 = true
  af_auth : before.getLsbD 10 ≠ after.getLsbD 10 → ha = true
  dirty_mono : after.getLsbD 7 = true → before.getLsbD 7 = true
  dirty_auth : before.getLsbD 7 ≠ after.getLsbD 7 →
    ha = true ∧ hd = true ∧ (pie = true ∨ before.getLsbD 51 = true)

namespace DescriptorDelta

theorem refl (ha hd pie : Bool) (d : BitVec 64) : DescriptorDelta ha hd pie d d :=
  ⟨fun _ _ _ _ => rfl, id, fun h => False.elim (h rfl), id, fun h => False.elim (h rfl)⟩

theorem trans (h : DescriptorDelta ha hd pie first second)
    (h' : DescriptorDelta ha hd pie second third) : DescriptorDelta ha hd pie first third := by
  refine ⟨fun i hi h7 h10 => (h'.fixed i hi h7 h10).trans (h.fixed i hi h7 h10),
    fun hf => h'.af_mono (h.af_mono hf), ?_,
    fun ht => h.dirty_mono (h'.dirty_mono ht), ?_⟩
  · intro hchange
    by_cases he : first.getLsbD 10 = second.getLsbD 10
    · exact h'.af_auth (fun he' => hchange (he.trans he'))
    · exact h.af_auth he
  · intro hchange
    by_cases he : first.getLsbD 7 = second.getLsbD 7
    · obtain ⟨hha, hhd, hp⟩ := h'.dirty_auth (fun he' => hchange (he.trans he'))
      refine ⟨hha, hhd, ?_⟩
      rw [h.fixed 51 (by decide) (by decide) (by decide)] at hp
      exact hp
    · exact h.dirty_auth he

/-- This readiness check is required in addition to a stable descriptor view. -/
def AFReady (ha : Bool) (d : BitVec 64) : Prop := d.getLsbD 10 = true ∨ ha = true

theorem af_ready (h : DescriptorDelta ha hd pie before after) (hr : AFReady ha before) :
    AFReady ha after := hr.elim (fun hf => Or.inl (h.af_mono hf)) Or.inr

theorem af_eq_of_disabled (h : DescriptorDelta ha hd pie before after) (hha : ha = false) :
    before.getLsbD 10 = after.getLsbD 10 := by
  by_cases he : before.getLsbD 10 = after.getLsbD 10
  · exact he
  · have := h.af_auth he
    simp [hha] at this

theorem dirty_eq_of_disabled (h : DescriptorDelta ha hd pie before after)
    (hdisabled : ha = false ∨ hd = false) : before.getLsbD 7 = after.getLsbD 7 := by
  by_cases he : before.getLsbD 7 = after.getLsbD 7
  · exact he
  · obtain ⟨hha, hhd, _⟩ := h.dirty_auth he
    rcases hdisabled with hh | hh
    · simp [hh] at hha
    · simp [hh] at hhd

/-- Disabling hardware AF updates also disables hardware dirty updates. -/
theorem eq_of_ha_disabled (h : DescriptorDelta ha hd pie before after) (hha : ha = false) :
    after = before := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h7 : i = 7
  · subst i
    exact (h.dirty_eq_of_disabled (Or.inl hha)).symm
  by_cases h10 : i = 10
  · subst i
    exact (h.af_eq_of_disabled hha).symm
  exact h.fixed i hi h7 h10

/-- Any slice avoiding the two mutable bits stays exactly equal, including
    descriptor kind, table/leaf output-address fields and DBM itself. -/
theorem slice_eq (h : DescriptorDelta ha hd pie before after) (start len : Nat)
    (hbound : start + len ≤ 64)
    (h7 : ∀ i < len, start + i ≠ 7) (h10 : ∀ i < len, start + i ≠ 10) :
    after.extractLsb' start len = before.extractLsb' start len := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  exact h.fixed (start + i) (by omega) (h7 i hi) (h10 i hi)

theorem address_bits (h : DescriptorDelta ha hd pie before after) :
    after.extractLsb' 12 36 = before.extractLsb' 12 36 :=
  h.slice_eq 12 36 (by decide) (by omega) (by omega)

theorem kind_bits (h : DescriptorDelta ha hd pie before after) :
    after.extractLsb' 0 2 = before.extractLsb' 0 2 :=
  h.slice_eq 0 2 (by decide) (by omega) (by omega)

end DescriptorDelta
#print axioms DescriptorDelta.trans
#print axioms DescriptorDelta.af_ready
#print axioms DescriptorDelta.eq_of_ha_disabled
#print axioms DescriptorDelta.address_bits
end ArmCert.Translate
