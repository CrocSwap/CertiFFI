import TranslateSpan.DefaultCurrent

open ArmBridge.Draft NativeMteTagCheck
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace TranslateSpan.DefaultMTE2

theorem rows_after_delta (entry current : NativeState) (capacity cost used : Nat)
    (rows : TagStatusRows entry (entry.choiceOcc.getD 1354 0) capacity)
    (delta : ChoiceDelta entry current used) (room : used + cost ≤ capacity) :
    TagStatusRows current (current.choiceOcc.getD 1354 0) cost := by
  intro index within
  unfold TagStatusRows at rows
  rw [delta.1, delta.2]
  simpa only [Nat.add_assoc] using rows (used + index) (by omega)

theorem bounded_rows (entry current : NativeState) (capacity limit cost : Nat)
    (rows : TagStatusRows entry (entry.choiceOcc.getD 1354 0) capacity)
    (trace : ∃ used, ChoiceDelta entry current used ∧ used ≤ limit)
    (room : limit + cost ≤ capacity) :
    TagStatusRows current (current.choiceOcc.getD 1354 0) cost := by
  obtain ⟨used, delta, bound⟩ := trace
  exact rows_after_delta entry current capacity cost used rows delta (by omega)

#print axioms rows_after_delta
#print axioms bounded_rows
end TranslateSpan.DefaultMTE2
