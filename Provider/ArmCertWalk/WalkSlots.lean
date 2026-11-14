-- v3 ask (a): the descriptor slots an actual walk reads are a COMPUTABLE function of the
-- declared logical rows and the VA (static `walk : BitVec 64 → List Nat`), under the decidable
-- condition that logical slot keys are unique. Mirrors PathChecker.walkPath.
import ArmCertTranslateModel.TopologyImage

open Sail ArmFull
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

/-- Declared slots read by the walk of `va` from `base` at `level` (table slots, then the leaf slot). -/
def walkSlots (rows : List LogicalRow) (va : BitVec 64) : Nat → Nat → Nat → BitVec 48 → List Nat
  | 0, _, _, _ => []
  | fuel + 1, level, bits, base =>
    match rows.find? (fun row => row.logical == S1LogicalReference.entryAddress base va level bits) with
    | none => []
    | some row =>
      match S1LogicalReference.descriptorKind level row.view.stable with
      | .ok .table => S1LogicalReference.entryAddress base va level bits ::
          walkSlots rows va fuel (level + 1) 9 (S1LogicalReference.childBase row.view)
      | _ => [S1LogicalReference.entryAddress base va level bits]

theorem find_logical_of_nodup (rows : List LogicalRow) (nodup : (rows.map (·.logical)).Nodup)
    (row : LogicalRow) (member : row ∈ rows) (key : Nat) (eq : row.logical = key) :
    rows.find? (fun r => r.logical == key) = some row := by
  induction rows with
  | nil => simp at member
  | cons head rest ih =>
    simp only [List.map_cons, List.nodup_cons] at nodup
    obtain ⟨fresh, restNodup⟩ := nodup
    rcases List.mem_cons.mp member with rfl | inRest
    · simp [eq]
    · have differs : head.logical ≠ key := by
        intro same
        apply fresh
        rw [same, ← eq]
        exact List.mem_map_of_mem inRest
      have notBeq : (head.logical == key) = false := by simpa using differs
      simp only [List.find?_cons, notBeq]
      exact ih restNodup inRest

/-- The observed row for a slot is the one `find?` returns, so its view is the observed view. -/
theorem find_observed (rows : List LogicalRow) (nodup : (rows.map (·.logical)).Nodup)
    (slot : Nat) (physical : FullAddress) (view : S1DescriptorPIE.View 64)
    (present : logicalObserve rows slot physical view) :
    ∃ row, rows.find? (fun r => r.logical == slot) = some row ∧ row.view = view := by
  obtain ⟨row, member, logical, _, viewEq⟩ := present
  exact ⟨row, find_logical_of_nodup rows nodup row member slot logical.symm, viewEq.symm⟩

theorem walk_slots_leaf (rows : List LogicalRow) (nodup : (rows.map (·.logical)).Nodup)
    (va : BitVec 64) (fuel level bits : Nat) (base : BitVec 48) (physical : FullAddress)
    (view : S1DescriptorPIE.View 64)
    (present : logicalObserve rows (S1LogicalReference.entryAddress base va level bits) physical view)
    (kind : S1LogicalReference.descriptorKind level view.stable = .ok .leaf) :
    walkSlots rows va (fuel + 1) level bits base = [S1LogicalReference.entryAddress base va level bits] := by
  obtain ⟨row, found, viewEq⟩ := find_observed rows nodup _ physical view present
  simp only [walkSlots, found, viewEq, kind]

theorem walk_slots_table (rows : List LogicalRow) (nodup : (rows.map (·.logical)).Nodup)
    (va : BitVec 64) (fuel level bits : Nat) (base : BitVec 48) (physical : FullAddress)
    (view : S1DescriptorPIE.View 64)
    (present : logicalObserve rows (S1LogicalReference.entryAddress base va level bits) physical view)
    (kind : S1LogicalReference.descriptorKind level view.stable = .ok .table) :
    walkSlots rows va (fuel + 1) level bits base =
      S1LogicalReference.entryAddress base va level bits ::
        walkSlots rows va fuel (level + 1) 9 (S1LogicalReference.childBase view) := by
  obtain ⟨row, found, viewEq⟩ := find_observed rows nodup _ physical view present
  simp only [walkSlots, found, viewEq, kind]

/-- Static declared slots of a query VA from the spec's layout root. -/
def declaredSlots (logicalRows : List LogicalRow) (layout : S1LogicalReference.Layout) (va : BitVec 64) : List Nat :=
  walkSlots logicalRows va (4 - layout.start) layout.start
    (S1LogicalReference.rootBits layout.start layout.inputBits) layout.root

#print axioms walk_slots_leaf
#print axioms walk_slots_table
end ArmCertWalk
