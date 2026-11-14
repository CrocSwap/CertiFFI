-- witness prep: build a TopologyImageSpec for a concrete program BY EVALUATION over its
-- finite declared rows and finite declared query list (domain = list membership). Every proof
-- field comes from a decidable check; `paths` uses the reference walk (walkPath_sound). No claims.
import ArmCertWalk.AccessDataBuilder
open Sail ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk

def nonSecureB (space : PASpace) : Bool :=
  match space with
  | .PAS_NonSecure => true
  | _ => false

theorem non_secure_sound {space : PASpace} (h : nonSecureB space = true) : space = .PAS_NonSecure := by
  cases space <;> simp_all [nonSecureB]

def logicalRowB (imageRows : List ImageRow) (row : LogicalRow) : Bool :=
  decide (row.logical % 8 = 0) && decide (row.physical.address.toNat % 8 = 0) &&
  decide (row.physical.address.extractLsb' 16 40 ≠ GIC_BASE.zeroExtend 40) &&
  decide (row.physical.address.extractLsb' 16 40 ≠ UART_BASE.zeroExtend 40) &&
  decide (row.logical = row.physical.address.toNat) && nonSecureB row.physical.paspace &&
  imageRows.any (fun image => decide (image.slot = row.physical.address.toNat) && decide (image.expected = row.view))

def checkSpecRows (logicalRows : List LogicalRow) (imageRows : List ImageRow) : Bool :=
  logicalRows.all (logicalRowB imageRows) && imageRows.all (fun image => decide (image.slot % 8 = 0))

def checkSpecQuery (physicalConfig : PhysicalConfig) (layout : S1LogicalReference.Layout)
    (logicalRows : List LogicalRow) (imageRows : List ImageRow) (fuel : Nat) (q : AccessQuery) : Bool :=
  decide (S1LogicalReference.entryAddress layout.root q.va layout.start
      (S1LogicalReference.rootBits layout.start layout.inputBits) < 2 ^ (effectiveBits physicalConfig).toNat) &&
  match walkPath logicalRows (effectiveBits physicalConfig).toNat q.va fuel layout.start
      (S1LogicalReference.rootBits layout.start layout.inputBits) layout.root with
  | some (.leaf _ _ physical view) => leafImageRowB imageRows physical.address.toNat view
  | _ => false

theorem logical_row_facts {imageRows : List ImageRow} {logicalRows : List LogicalRow}
    (checked : checkSpecRows logicalRows imageRows = true) {row : LogicalRow} (member : row ∈ logicalRows) :
    row.logical % 8 = 0 ∧ row.physical.address.toNat % 8 = 0 ∧ S2TableRAM.OrdinaryRAM row.physical.address ∧
      row.logical = row.physical.address.toNat ∧ row.physical.paspace = .PAS_NonSecure ∧
      ∃ image ∈ imageRows, image.slot = row.physical.address.toNat ∧ image.expected = row.view := by
  simp only [checkSpecRows, Bool.and_eq_true, List.all_eq_true] at checked
  have each := checked.1 row member
  simp only [logicalRowB, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at each
  obtain ⟨⟨⟨⟨⟨⟨logicalAligned, physicalAligned⟩, notGIC⟩, notUART⟩, ident⟩, space⟩, image, member', slot, view⟩ := each
  exact ⟨logicalAligned, physicalAligned, ⟨notGIC, notUART⟩, ident, non_secure_sound space, image, member', slot, view⟩

/-- **TopologyImageSpec by evaluation** over a finite declared query list. -/
noncomputable def specOfChecks (params : S1TTWParams) (physicalConfig : PhysicalConfig)
    (controls : S1LogicalReference.Controls) (layout : S1LogicalReference.Layout)
    (logicalRows : List LogicalRow) (imageRows : List ImageRow) (queries : List AccessQuery) (fuel : Nat)
    (rowsOK : checkSpecRows logicalRows imageRows = true)
    (queriesOK : queries.all (checkSpecQuery physicalConfig layout logicalRows imageRows fuel) = true) :
    TopologyImageSpec (fun q => q ∈ queries) where
  params := params
  physicalConfig := physicalConfig
  controls := controls
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

end ArmCertWalk
