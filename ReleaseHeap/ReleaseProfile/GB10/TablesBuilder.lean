import ReleaseProfile.GB10.SpecWitness
import ArmCertWalk.SpecBuilder
import ArmCertWalk.PageTransfer

set_option autoImplicit false

/-!
# Tables-only topology data from finite checks

`ArmCertWalk.specOfChecks(Page)` builds a whole `TopologyImageSpec`, including params/controls supplied
by the caller. The C2 world must not choose those, so this builds the tables-only `GB10.TopologyTables`
(at `gb10Physical`) from the same decidable row/query checks, with the same proofs and no params/controls.
-/

namespace ReleaseProfile.GB10.TablesBuilder

open ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ReleaseProfile.GB10

/-- Tables for the exact query list. -/
noncomputable def tablesOfChecks (layout : S1LogicalReference.Layout) (logicalRows : List LogicalRow)
    (imageRows : List ImageRow) (queries : List AccessQuery) (fuel : Nat)
    (rowsOK : checkSpecRows logicalRows imageRows = true)
    (queriesOK : queries.all (checkSpecQuery gb10Physical layout logicalRows imageRows fuel) = true) :
    TopologyTables (fun q => q ∈ queries) where
  layout := layout
  logicalRows := logicalRows
  imageRows := imageRows
  available := by
    rintro logical physical view ⟨row, member, rfl, rfl, rfl⟩
    obtain ⟨a, b, c, _⟩ := logical_row_facts rowsOK member
    exact ⟨a, b, c⟩
  identity := by
    rintro logical physical view ⟨row, member, rfl, rfl, rfl⟩
    obtain ⟨_, _, _, d, e, _⟩ := logical_row_facts rowsOK member
    exact ⟨d, e⟩
  represented := by
    rintro logical physical view ⟨row, member, rfl, rfl, rfl⟩
    obtain ⟨_, _, _, _, _, image, imageMember, slot, view⟩ := logical_row_facts rowsOK member
    exact ⟨image.leaf, image, imageMember, slot.symm, rfl, view.symm⟩
  aligned := by
    rintro slot leaf view ⟨image, member, rfl, _, _⟩
    simp only [checkSpecRows, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at rowsOK
    exact rowsOK.2 image member
  rootBound := by
    intro q member
    have each := List.all_eq_true.mp queriesOK q member
    simp only [checkSpecQuery, Bool.and_eq_true, decide_eq_true_eq] at each
    exact each.1
  paths := by
    intro q member
    have each := List.all_eq_true.mp queriesOK q member
    simp only [checkSpecQuery, Bool.and_eq_true] at each
    obtain ⟨_, walked⟩ := each
    split at walked
    · rename_i leafLevel logical physical view found
      exact ⟨leafLevel, logical, physical, view,
        walkPath_sound _ _ _ _ _ _ _ _ _ _ _ found, leaf_image_row_sound _ _ _ walked⟩
    · simp at walked

/-- Tables keyed by page: every query whose VA lies in a declared query's 4KiB page. -/
noncomputable def tablesOfChecksPage (layout : S1LogicalReference.Layout) (logicalRows : List LogicalRow)
    (imageRows : List ImageRow) (queries : List AccessQuery) (fuel : Nat)
    (rowsOK : checkSpecRows logicalRows imageRows = true)
    (queriesOK : queries.all (checkSpecQuery gb10Physical layout logicalRows imageRows fuel) = true) :
    TopologyTables (fun q => ∃ q0 ∈ queries, SamePage q0.va q.va) :=
  let base := tablesOfChecks layout logicalRows imageRows queries fuel rowsOK queriesOK
  { base with
    rootBound := by
      rintro q ⟨q0, member, same⟩
      rw [← entryAddress_page same]; exact base.rootBound q0 member
    paths := by
      rintro q ⟨q0, member, same⟩
      obtain ⟨level, logical, physical, view, path, used⟩ := base.paths q0 member
      exact ⟨level, logical, physical, view, path_page same path, used⟩ }

end ReleaseProfile.GB10.TablesBuilder

#print axioms ReleaseProfile.GB10.TablesBuilder.tablesOfChecksPage
