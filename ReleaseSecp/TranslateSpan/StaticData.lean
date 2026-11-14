-- Pure bounded topology and access certificates, built from declared logical rows.
-- No machine State or state-indexed callback is an input to these constructors.
import ArmCertWalk.SpecBuilder
import TranslateSpan.QueryDescriptors
open Sail ArmFull ArmFull.Functions ArmCertWalk ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 4096
namespace TranslateSpan.StaticData

-- Frozen Sail enums provide equality through computable constructor cases.
private def accessTypeDecEq : DecidableEq AccessType := by
  intro a b
  cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (fun h => by cases h)
private def rangeDecEq : DecidableEq VARange := by
  intro a b
  cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (fun h => by cases h)
private def securityDecEq : DecidableEq SecurityState := by
  intro a b
  cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (fun h => by cases h)
attribute [local instance] accessTypeDecEq rangeDecEq securityDecEq

def canonical (va : BitVec 64) : AccessQuery :=
  ⟨va,⟨QueryDescriptors.data false,false⟩,1⟩

/-- Raw descriptors, flags and sizes do not restrict this finite VA domain. -/
noncomputable def specOfVAChecks (params : S1TTWParams) (physicalConfig : PhysicalConfig)
    (controls : S1LogicalReference.Controls) (layout : S1LogicalReference.Layout)
    (logicalRows : List LogicalRow) (imageRows : List ImageRow) (addresses : List (BitVec 64)) (fuel : Nat)
    (rowsOK : checkSpecRows logicalRows imageRows = true)
    (queriesOK : (addresses.map canonical).all (checkSpecQuery physicalConfig layout logicalRows imageRows fuel) = true) :
    TopologyImageSpec (fun q => q.va ∈ addresses) :=
  let old := specOfChecks params physicalConfig controls layout logicalRows imageRows
    (addresses.map canonical) fuel rowsOK queriesOK
  { params := params, physicalConfig := physicalConfig, controls := controls, layout := layout
    logicalRows := logicalRows, imageRows := imageRows
    available := old.available
    identity := old.identity
    represented := old.represented
    aligned := old.aligned
    rootBound := by
      intro q member
      exact old.rootBound (canonical q.va) (List.mem_map.mpr ⟨q.va,member,rfl⟩)
    paths := by
      intro q member
      exact old.paths (canonical q.va) (List.mem_map.mpr ⟨q.va,member,rfl⟩) }

def checkTopology (cap : Nat) (physicalConfig : PhysicalConfig) (layout : S1LogicalReference.Layout)
    (logicalRows : List LogicalRow) (imageRows : List ImageRow) (addresses : List (BitVec 64)) (fuel : Nat) : Bool :=
  decide (addresses.length ≤ cap) && checkSpecRows logicalRows imageRows &&
    (addresses.map canonical).all (checkSpecQuery physicalConfig layout logicalRows imageRows fuel)

noncomputable def specOfCheckedVA (cap : Nat) (params : S1TTWParams) (physicalConfig : PhysicalConfig)
    (controls : S1LogicalReference.Controls) (layout : S1LogicalReference.Layout)
    (logicalRows : List LogicalRow) (imageRows : List ImageRow) (addresses : List (BitVec 64)) (fuel : Nat)
    (checked : checkTopology cap physicalConfig layout logicalRows imageRows addresses fuel = true) :
    TopologyImageSpec (fun q => q.va ∈ addresses) := by
  have checks := checked
  simp only [checkTopology,Bool.and_eq_true,decide_eq_true_eq] at checks
  exact specOfVAChecks params physicalConfig controls layout logicalRows imageRows addresses fuel checks.1.2 checks.2

def permissionCandidate {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (q : AccessQuery) (fuel : Nat)
    (physical : FullAddress) (view : S1DescriptorPIE.View 64) : Option PermissionRow :=
  rows.find? (fun row => permissionRowB spec config q physical view
    (walkWords spec.logicalRows (effectiveBits spec.physicalConfig).toNat q.va fuel spec.layout.start
      (S1LogicalReference.rootBits spec.layout.start spec.layout.inputBits) spec.layout.root) row &&
      decide (row.access.acctype = q.request.raw.acctype))

def checkData {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (q : AccessQuery) (fuel : Nat) : Bool :=
  (decide (AArch64_GetVARange q.va = .VARange_LOWER) &&
    (decide (q.request.raw.el = EL0) && decide (q.request.raw.ss = .SS_NonSecure))) &&
  match walkPath spec.logicalRows (effectiveBits spec.physicalConfig).toNat q.va fuel spec.layout.start
      (S1LogicalReference.rootBits spec.layout.start spec.layout.inputBits) spec.layout.root with
  | some (.leaf _ _ physical view) => (permissionCandidate spec config rows q fuel physical view).isSome
  | _ => false

/-- Every data field comes from the reference walk or a finite row lookup.
Unsupported paths and missing/invalid permission rows cannot construct data. -/
noncomputable def dataOfCheck {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (q : AccessQuery) (fuel : Nat)
    (checked : checkData spec config rows q fuel = true) : S1AccessData spec config rows q := by
  have checks := checked
  simp only [checkData,Bool.and_eq_true,decide_eq_true_eq] at checks
  obtain ⟨⟨lower,accessEL,nonsecure⟩,found⟩ := checks
  cases walked : walkPath spec.logicalRows (effectiveBits spec.physicalConfig).toNat q.va fuel spec.layout.start
      (S1LogicalReference.rootBits spec.layout.start spec.layout.inputBits) spec.layout.root with
  | none => simp only [walked] at found; contradiction
  | some result =>
    cases result with
    | translationFault level => simp only [walked] at found; contradiction
    | addressSizeFault level => simp only [walked] at found; contradiction
    | leaf leafLevel logical physical view =>
      cases chosen : permissionCandidate spec config rows q fuel physical view with
      | none => simp only [walked,chosen,Option.isSome_none] at found; contradiction
      | some row =>
        unfold permissionCandidate at chosen
        have member := List.mem_of_find?_eq_some chosen
        have selected := List.find?_some chosen
        simp only [Bool.and_eq_true,decide_eq_true_eq] at selected
        exact accessDataOfWalk spec config rows q fuel leafLevel logical physical view walked
          row member selected.1 selected.2 lower accessEL nonsecure

#print axioms canonical
#print axioms specOfVAChecks
#print axioms checkTopology
#print axioms specOfCheckedVA
#print axioms permissionCandidate
#print axioms checkData
#print axioms dataOfCheck
end TranslateSpan.StaticData
