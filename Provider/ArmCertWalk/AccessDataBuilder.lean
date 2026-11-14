-- witness prep: build the per-query S1AccessData (Path + PathPermissionUse + query facts)
-- of a concrete program BY EVALUATION: a successful reference walk over the declared logical
-- rows and a declared permission row passing a decidable check. No claims; no new premise.
import ArmCertWalk.PathChecker
import ArmCertTranslateModel.TranslationInvariant
open Sail ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk

/-- Decidable form of `rowsObserve rows slot true view`. -/
def leafImageRowB (rows : List ImageRow) (slot : Nat) (view : S1DescriptorPIE.View 64) : Bool :=
  rows.any (fun row => decide (row.slot = slot) && row.leaf && decide (row.expected = view))

theorem leaf_image_row_sound (rows : List ImageRow) (slot : Nat) (view : S1DescriptorPIE.View 64)
    (h : leafImageRowB rows slot view = true) : rowsObserve rows slot true view := by
  obtain ⟨row, member, ok⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ok
  exact ⟨row, member, ok.1.1.symm, ok.1.2.symm, ok.2.symm⟩

/-- Decidable checks a declared permission row must pass for the walked leaf. -/
def permissionRowB {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (query : AccessQuery) (physical : FullAddress) (view : S1DescriptorPIE.View 64)
    (words : List (BitVec 64)) (row : PermissionRow) : Bool :=
  decide (row.slot = physical.address.toNat) &&
  decide (row.prior = words.foldl (fun previous word =>
    S1LogicalReference.tablePermissions spec.controls previous word) ⟨0#2, false, false⟩) &&
  leafImageRowB spec.imageRows physical.address.toNat view &&
  decide (S1DescriptorPIE.view (spec.params.pie == 1#1) (spec.params.ha == 1#1) (spec.params.hd == 1#1) row.raw = view) &&
  checkPermissionRowAttributes config spec.params row &&
  decide (row.access.read = query.request.raw.read) &&
  decide (row.access.write = query.request.raw.write) &&
  decide (row.access.tagaccess = query.request.raw.tagaccess)

/-- **S1AccessData by evaluation.** -/
noncomputable def accessDataOfWalk {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (query : AccessQuery) (fuel : Nat)
    (leafLevel logical : Nat) (physical : FullAddress) (view : S1DescriptorPIE.View 64)
    (walked : walkPath spec.logicalRows (effectiveBits spec.physicalConfig).toNat query.va fuel
      spec.layout.start (S1LogicalReference.rootBits spec.layout.start spec.layout.inputBits) spec.layout.root =
      some (.leaf leafLevel logical physical view))
    (row : PermissionRow) (member : row ∈ rows)
    (rowOK : permissionRowB spec config query physical view
      (walkWords spec.logicalRows (effectiveBits spec.physicalConfig).toNat query.va fuel spec.layout.start
        (S1LogicalReference.rootBits spec.layout.start spec.layout.inputBits) spec.layout.root) row = true)
    (kind : row.access.acctype = query.request.raw.acctype)
    (lower : AArch64_GetVARange query.va = .VARange_LOWER)
    (accessEL : query.request.raw.el = EL0) (nonsecure : query.request.raw.ss = .SS_NonSecure) :
    S1AccessData spec config rows query :=
  have path := walkPath_sound _ _ _ _ _ _ _ _ _ _ _ walked
  have checks := rowOK
  { leafLevel := leafLevel, logical := logical, physical := physical, view := view, path := path,
    permissions :=
      { row := row, member := member
        slot := by
          simp only [permissionRowB, Bool.and_eq_true, decide_eq_true_eq] at checks
          exact checks.1.1.1.1.1.1.1
        words := walkWords spec.logicalRows (effectiveBits spec.physicalConfig).toNat query.va fuel spec.layout.start
          (S1LogicalReference.rootBits spec.layout.start spec.layout.inputBits) spec.layout.root
        annotation := by
          obtain ⟨_, annotated⟩ := walkPath_annotated _ _ _ spec.controls _ _ _ _ _ _ _ _ walked
          simp only [permissionRowB, Bool.and_eq_true, decide_eq_true_eq] at checks
          rw [checks.1.1.1.1.1.1.2]
          exact annotated ⟨0#2, false, false⟩
        used := by
          simp only [permissionRowB, Bool.and_eq_true, decide_eq_true_eq] at checks
          exact leaf_image_row_sound _ _ _ checks.1.1.1.1.1.2
        rowView := by
          simp only [permissionRowB, Bool.and_eq_true, decide_eq_true_eq] at checks
          exact checks.1.1.1.1.2
        attributes := by
          simp only [permissionRowB, Bool.and_eq_true, decide_eq_true_eq] at checks
          exact checks.1.1.1.2
        kind := kind
        read := by
          simp only [permissionRowB, Bool.and_eq_true, decide_eq_true_eq] at checks
          exact checks.1.1.2
        write := by
          simp only [permissionRowB, Bool.and_eq_true, decide_eq_true_eq] at checks
          exact checks.1.2
        tagaccess := by
          simp only [permissionRowB, Bool.and_eq_true, decide_eq_true_eq] at checks
          exact checks.2 },
    lower := lower, accessEL := accessEL, nonsecure := nonsecure }

end ArmCertWalk
