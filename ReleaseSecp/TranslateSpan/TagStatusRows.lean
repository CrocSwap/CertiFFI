import NativeMteTagCheck.Primitive

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
attribute [local implicit_reducible] oracleChoiceSource

namespace TranslateSpan.TagStatusRows
open NativeMteTagCheck

def check (capacity : Nat) (entry : State) : Bool :=
  (List.range capacity).all fun offset =>
    entry.choiceState.1
      (((ChoiceLabel.occ 1354 (entry.choiceOcc.getD 1354 0 + offset)).child 0).child 0)
      (.fin 23) == 0

theorem of_check (capacity : Nat) (entry : State) (checked : check capacity entry = true) :
    NativeMteTagCheck.TagStatusRows entry (entry.choiceOcc.getD 1354 0) capacity := by
  intro index inside
  have row := List.all_eq_true.mp checked _ (List.mem_range.mpr inside)
  exact beq_iff_eq.mp row

theorem status_at_current (capacity used : Nat) (entry current : State)
    (checked : check capacity entry = true) (delta : ChoiceDelta entry current used)
    (within : used < capacity) : TagStatusOK current :=
  tag_status_of_rows entry current _ capacity used (of_check capacity entry checked)
    delta.1 delta.2 within

theorem remaining (capacity used : Nat) (entry current : State)
    (checked : check capacity entry = true) (bound : used ≤ capacity)
    (delta : ChoiceDelta entry current used) : check (capacity - used) current = true := by
  apply List.all_eq_true.mpr
  intro offset member
  have inside := List.mem_range.mp member
  apply beq_iff_eq.mpr
  change current.choiceState.1
    (((ChoiceLabel.occ 1354 (current.choiceOcc.getD 1354 0 + offset)).child 0).child 0)
    (.fin 23) = 0
  rw [delta.1, delta.2, Nat.add_assoc]
  exact of_check capacity entry checked (used + offset) (by omega)

#print axioms of_check
#print axioms status_at_current
#print axioms remaining
end TranslateSpan.TagStatusRows
