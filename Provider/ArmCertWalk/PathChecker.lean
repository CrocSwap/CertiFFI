-- Executable reference walk over the DECLARED logical rows and its soundness: a successful
-- evaluation yields the existing S1LogicalReference.Path proof (Prop) for a concrete program.
-- Used to build S1AccessData by evaluation (witness prep; folds checks into its
-- aggregate). No source-call claim: Path is the existing presence/topology certificate.
import ArmCertTranslateModel.TopologyImage
import ArmCertWalk.PathPermissionAnnotation
open Sail ArmFull
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk

/-- Reference walk: follow declared rows from `base` at `level` for VA `va`. -/
def walkPath (rows : List LogicalRow) (paBits : Nat) (va : BitVec 64) :
    Nat → Nat → Nat → BitVec 48 → Option S1LogicalReference.PathEnd
  | 0, _, _, _ => none
  | fuel + 1, level, bits, base =>
    match rows.find? (fun row => row.logical == S1LogicalReference.entryAddress base va level bits) with
    | none => none
    | some row =>
      if S1LogicalReference.entryAddress base va level bits % 8 = 0 then
        match S1LogicalReference.descriptorKind level row.view.stable with
        | .ok .leaf =>
          if level ≤ 3 then
            some (.leaf level (S1LogicalReference.entryAddress base va level bits) row.physical row.view)
          else none
        | .ok .table =>
          if level < 3 ∧ S1LogicalReference.entryAddress (S1LogicalReference.childBase row.view) va (level + 1) 9
              < 2 ^ paBits then
            walkPath rows paBits va fuel (level + 1) 9 (S1LogicalReference.childBase row.view)
          else none
        | _ => none
      else none

theorem walkPath_sound (rows : List LogicalRow) (paBits : Nat) (va : BitVec 64) :
    ∀ (fuel level bits : Nat) (base : BitVec 48) (leafLevel logical : Nat) (physical : FullAddress)
      (view : S1DescriptorPIE.View 64),
      walkPath rows paBits va fuel level bits base = some (.leaf leafLevel logical physical view) →
      S1LogicalReference.Path (logicalObserve rows) paBits va level bits base
        (.leaf leafLevel logical physical view) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ h; simp [walkPath] at h
  | succ fuel ih =>
    intro level bits base leafLevel logical physical view h
    simp only [walkPath] at h
    split at h
    · simp at h
    · rename_i row found
      have member := List.mem_of_find?_eq_some found
      have matched : row.logical = S1LogicalReference.entryAddress base va level bits := by
        have := List.find?_some found
        simpa using this
      have present : logicalObserve rows (S1LogicalReference.entryAddress base va level bits) row.physical row.view :=
        ⟨row, member, matched.symm, rfl, rfl⟩
      split at h
      · rename_i aligned
        split at h
        · rename_i kind
          split at h
          · rename_i hl
            simp only [Option.some.injEq, S1LogicalReference.PathEnd.leaf.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            exact .leaf level bits base row.physical row.view hl aligned present kind
          · simp at h
        · rename_i kind
          split at h
          · rename_i bounds
            exact .table level bits base row.physical row.view _ bounds.1 aligned present kind bounds.2
              (ih (level + 1) 9 (S1LogicalReference.childBase row.view) leafLevel logical physical view h)
          · simp at h
        · simp at h
      · simp at h

/-- Stable words of the table descriptors the reference walk traverses, in order. -/
def walkWords (rows : List LogicalRow) (paBits : Nat) (va : BitVec 64) :
    Nat → Nat → Nat → BitVec 48 → List (BitVec 64)
  | 0, _, _, _ => []
  | fuel + 1, level, bits, base =>
    match rows.find? (fun row => row.logical == S1LogicalReference.entryAddress base va level bits) with
    | none => []
    | some row =>
      match S1LogicalReference.descriptorKind level row.view.stable with
      | .ok .table => row.view.stable ::
          walkWords rows paBits va fuel (level + 1) 9 (S1LogicalReference.childBase row.view)
      | _ => []

/-- A successful reference walk yields a Path together with its permission
annotation, whose words are `walkWords` and whose final prior is their fold. -/
theorem walkPath_annotated (rows : List LogicalRow) (paBits : Nat) (va : BitVec 64)
    (controls : S1LogicalReference.Controls) :
    ∀ (fuel level bits : Nat) (base : BitVec 48) (leafLevel logical : Nat) (physical : FullAddress)
      (view : S1DescriptorPIE.View 64),
      walkPath rows paBits va fuel level bits base = some (.leaf leafLevel logical physical view) →
      ∃ path : S1LogicalReference.Path (logicalObserve rows) paBits va level bits base
          (.leaf leafLevel logical physical view),
        ∀ prior, PathPermissionAnnotation (logicalObserve rows) paBits va controls path prior
          (walkWords rows paBits va fuel level bits base)
          ((walkWords rows paBits va fuel level bits base).foldl
            (fun previous word => S1LogicalReference.tablePermissions controls previous word) prior) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ h; simp [walkPath] at h
  | succ fuel ih =>
    intro level bits base leafLevel logical physical view h
    simp only [walkPath] at h
    simp only [walkWords]
    split at h
    · simp at h
    · rename_i row found
      have member := List.mem_of_find?_eq_some found
      have matched : row.logical = S1LogicalReference.entryAddress base va level bits := by
        have := List.find?_some found
        simpa using this
      have present : logicalObserve rows (S1LogicalReference.entryAddress base va level bits) row.physical row.view :=
        ⟨row, member, matched.symm, rfl, rfl⟩
      split at h
      · rename_i aligned
        split at h
        · rename_i kind
          split at h
          · rename_i hl
            simp only [Option.some.injEq, S1LogicalReference.PathEnd.leaf.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            simp only [kind]
            exact ⟨.leaf level bits base row.physical row.view hl aligned present kind, fun prior =>
              .leaf level bits base row.physical row.view hl aligned present kind prior⟩
          · simp at h
        · rename_i kind
          split at h
          · rename_i bounds
            simp only [kind]
            obtain ⟨tail, tailAnnotation⟩ :=
              ih (level + 1) 9 (S1LogicalReference.childBase row.view) leafLevel logical physical view h
            refine ⟨.table level bits base row.physical row.view _ bounds.1 aligned present kind bounds.2 tail,
              fun prior => ?_⟩
            simp only [List.foldl_cons]
            exact .table level bits base row.physical row.view _ bounds.1 aligned present kind bounds.2 tail
              prior _ _ (tailAnnotation (S1LogicalReference.tablePermissions controls prior row.view.stable))
          · simp at h
        · simp at h
      · simp at h

#print axioms walkPath_sound
#print axioms walkPath_annotated
end ArmCertWalk
