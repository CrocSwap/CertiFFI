import ArmCertTranslateModel.CurrentS1Checks
import NativeSourceInit.PhysicalPlan

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- The eight little-endian physical bytes of one raw descriptor at its slot. -/
def descriptorBytes (slot : Nat) (raw : BitVec 64) : NativeSourceInit.Plan :=
  (List.range 8).map fun i => (slot + i, raw.extractLsb' (8 * i) 8)

/-- Plan rows for every declared descriptor row. -/
def imageRowsPlan (rows : List ImageRow) : NativeSourceInit.Plan :=
  rows.flatMap fun row => descriptorBytes row.slot row.raw

/-- A memory satisfying a plan that contains a descriptor's bytes passes the
    byte comparison both image and permission checks perform. -/
theorem descriptor_bytes_check {plan : NativeSourceInit.Plan} {mem : Mem} {slot : Nat}
    {raw : BitVec 64} (satisfied : NativeSourceInit.Satisfies plan mem)
    (covered : ∀ row ∈ descriptorBytes slot raw, row ∈ plan) :
    (List.range 8).all (fun i => decide (mem[slot + i]? = some (raw.extractLsb' (8 * i) 8))) = true := by
  apply List.all_eq_true.2
  intro i member
  apply decide_eq_true
  exact satisfied _ (covered _ (List.mem_map.2 ⟨i, member, rfl⟩))

/-- `List.all` congruence using membership. -/
theorem all_congr_mem {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.all_cons, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- Memory-free part of one image-row check. -/
def ImageRow.checkPure (row : ImageRow) (pie ha hd : Bool) : Bool :=
  decide (S1DescriptorPIE.view pie ha hd row.raw = row.expected) &&
  (!row.leaf || row.raw.getLsbD 10 || ha) && decide (row.slot % 8 = 0)

def checkImagePure (rows : List ImageRow) (pie ha hd : Bool) : Bool :=
  rows.all fun row => row.checkPure pie ha hd

/-- Memory-free part of one permission-row check. -/
def PermissionRow.checkPure (row : PermissionRow) (params : S1TTWParams) (regs : Regs)
    (controls : S1LogicalReference.Controls) : Bool :=
  decide (row.slot % 8 = 0) &&
  checkCanonicalAdmission params regs (descriptorPermissionView controls row.prior row.raw)
    row.attributes row.access row.witness

def checkPermissionImagePure (rows : List PermissionRow) (params : S1TTWParams) (regs : Regs)
    (controls : S1LogicalReference.Controls) : Bool :=
  rows.all fun row => row.checkPure params regs controls

theorem checkImage_of_satisfies {rows : List ImageRow} {pie ha hd : Bool} {plan : NativeSourceInit.Plan}
    {mem : Mem} (satisfied : NativeSourceInit.Satisfies plan mem)
    (covered : ∀ row ∈ imageRowsPlan rows, row ∈ plan) :
    checkImage rows pie ha hd mem = checkImagePure rows pie ha hd := by
  unfold checkImage checkImagePure
  apply all_congr_mem
  intro row member
  have bytes := descriptor_bytes_check (slot := row.slot) (raw := row.raw) satisfied
    (fun b hb => covered b (List.mem_flatMap.2 ⟨row, member, hb⟩))
  simp only [ImageRow.check, ImageRow.checkPure, bytes, Bool.true_and]

/-- Permission rows must name declared descriptor rows (checkable, finite). -/
def PermissionRowsDeclared (rows : List PermissionRow) (imageRows : List ImageRow) : Prop :=
  ∀ row ∈ rows, ∃ image ∈ imageRows, image.slot = row.slot ∧ image.raw = row.raw

theorem checkPermissionImage_of_satisfies {rows : List PermissionRow} {imageRows : List ImageRow}
    {params : S1TTWParams} {regs : Regs} {controls : S1LogicalReference.Controls}
    {plan : NativeSourceInit.Plan} {mem : Mem} (satisfied : NativeSourceInit.Satisfies plan mem)
    (covered : ∀ row ∈ imageRowsPlan imageRows, row ∈ plan)
    (declared : PermissionRowsDeclared rows imageRows) :
    checkPermissionImage rows params regs controls mem = checkPermissionImagePure rows params regs controls := by
  unfold checkPermissionImage checkPermissionImagePure
  apply all_congr_mem
  intro row member
  obtain ⟨image, imageMember, slot, raw⟩ := declared row member
  have bytes := descriptor_bytes_check (slot := row.slot) (raw := row.raw) satisfied (fun b hb =>
    covered b (List.mem_flatMap.2 ⟨image, imageMember, by rw [slot, raw]; exact hb⟩))
  simp only [PermissionRow.check, PermissionRow.checkPure, bytes, Bool.true_and]

/-- The memory-free form of `checkCurrentS1`: registers and pure row data only. -/
def checkCurrentS1Pure {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (regs : Regs) : Bool :=
  checkPermissionRowsCovered rows (rowsFootprint spec.imageRows) &&
  (checkImagePure spec.imageRows (spec.params.pie == 1#1) (spec.params.ha == 1#1) (spec.params.hd == 1#1) &&
  (checkAttributeImage spec.imageRows config &&
  (checkWriteBackAttributeImage spec.imageRows config &&
  (checkPermissionImagePure rows spec.params regs spec.controls &&
  (checkHostWalk config spec.controls spec.physicalConfig regs &&
  (checkHostImageParams regs
      {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (regs.bank_BitVec_64 .TCR_EL2)} &&
  (checkNormalizedTxsz regs spec.params &&
  (checkHostTranslateGuard regs spec.params &&
  (decide (sourceTxszFault regs
      {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (regs.bank_BitVec_64 .TCR_EL2)} = false) &&
  (currentTranslationEnabled regs &&
  decide (regs.bank_Bool .__tlb_enabled = false)))))))))))

/-- On any state whose RAM satisfies a plan holding every declared descriptor's
    bytes (and whose permission rows name declared descriptors), `checkCurrentS1`
    is its memory-free form on the registers. -/
theorem checkCurrentS1_of_satisfies {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (state : State)
    {plan : NativeSourceInit.Plan} (satisfied : NativeSourceInit.Satisfies plan state.mem)
    (covered : ∀ row ∈ imageRowsPlan spec.imageRows, row ∈ plan)
    (declared : PermissionRowsDeclared rows spec.imageRows) :
    checkCurrentS1 spec config rows state = checkCurrentS1Pure spec config rows state.regs := by
  unfold checkCurrentS1 checkCurrentS1Pure
  rw [checkImage_of_satisfies satisfied covered, checkPermissionImage_of_satisfies satisfied covered declared]

/-- Current invariant on a plan-materialized state from memory-free checks. -/
theorem current_s1_of_plan {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (state : State)
    {plan : NativeSourceInit.Plan} (satisfied : NativeSourceInit.Satisfies plan state.mem)
    (covered : ∀ row ∈ imageRowsPlan spec.imageRows, row ∈ plan)
    (declared : PermissionRowsDeclared rows spec.imageRows)
    (checked : checkCurrentS1Pure spec config rows state.regs = true) :
    CurrentS1At spec config rows state :=
  current_s1_of_check spec config rows state
    ((checkCurrentS1_of_satisfies spec config rows state satisfied covered declared).trans checked)

#print axioms checkImage_of_satisfies
#print axioms checkPermissionImage_of_satisfies
#print axioms checkCurrentS1_of_satisfies
#print axioms current_s1_of_plan
end ArmCert.Translate.Model
