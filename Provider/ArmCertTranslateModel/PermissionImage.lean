import ArmCertTranslateModel.CanonicalAdmission
import ArmCertTranslateModel.StoreHistory
import ArmCertTranslateModel.GuardedPageFrame

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

/-- One finite permission use. The same slot may have several uses, accesses,
    or inherited table restrictions. The raw word and permission witness are
    initialization data, not values frozen across hardware updates.

    The native walk must link prior/attributes/access to its actual path and
    current results. This row does not assert that linkage or source success. -/
structure PermissionRow where
  slot : Nat
  raw : BitVec 64
  prior : S1LogicalReference.TablePermissions
  attributes : AttributeBody
  access : AccessDescriptor
  witness : ArmFull.Permissions

def PermissionRow.check (row : PermissionRow) (params : S1TTWParams) (regs : Regs)
    (controls : S1LogicalReference.Controls) (mem : Mem) : Bool :=
  (List.range 8).all (fun i => decide (mem[row.slot + i]? = some (row.raw.extractLsb' (8 * i) 8))) &&
  decide (row.slot % 8 = 0) &&
  checkCanonicalAdmission params regs (descriptorPermissionView controls row.prior row.raw)
    row.attributes row.access row.witness

def checkPermissionImage (rows : List PermissionRow) (params : S1TTWParams) (regs : Regs)
    (controls : S1LogicalReference.Controls) (mem : Mem) : Bool :=
  rows.all (fun row => row.check params regs controls mem)

/-- Current bytes and permission admission at each finite use. There is no
    future state, call, preservation law or unknown source answer in the image. -/
def PermissionImage (rows : List PermissionRow) (params : S1TTWParams) (regs : Regs)
    (controls : S1LogicalReference.Controls) (mem : Mem) : Prop :=
  ∀ row ∈ rows, row.slot % 8 = 0 ∧ ∃ d, S1ByteMemory.DescAt mem row.slot d ∧
    CanonicalAdmission params regs (descriptorPermissionView controls row.prior d) row.attributes row.access

def permissionRowsFootprint (rows : List PermissionRow) : Footprint :=
  ⟨rows.map PermissionRow.slot, 8⟩

theorem check_permission_image_sound (rows : List PermissionRow) (params : S1TTWParams) (regs : Regs)
    (controls : S1LogicalReference.Controls) (mem : Mem)
    (checked : checkPermissionImage rows params regs controls mem = true) :
    PermissionImage rows params regs controls mem := by
  intro row member
  have entry := (List.all_eq_true.mp checked) row member
  simp only [PermissionRow.check, Bool.and_eq_true, decide_eq_true_eq] at entry
  obtain ⟨⟨bytes, aligned⟩, admitted⟩ := entry
  refine ⟨aligned, row.raw, ?_, check_canonical_admission_sound _ _ _ _ _ _ admitted⟩
  intro i bound
  exact of_decide_eq_true ((List.all_eq_true.mp bytes) i (List.mem_range.mpr bound))

/-- Recover admission for the actual current descriptor, rather than the
    initialization word retained in the finite row. -/
theorem PermissionImage.admission
    (image : PermissionImage rows params regs controls mem) (row : PermissionRow) (member : row ∈ rows)
    (d : BitVec 64) (present : S1ByteMemory.DescAt mem row.slot d) :
    CanonicalAdmission params regs (descriptorPermissionView controls row.prior d) row.attributes row.access := by
  obtain ⟨_, current, bytes, admitted⟩ := image row member
  have equal := S1ByteMemory.descriptor_unique mem row.slot current d bytes present
  simpa only [equal] using admitted

theorem PermissionImage.hardware_store
    (image : PermissionImage rows params regs controls mem)
    (ha : controls.ha = (params.ha == 1#1)) (hd : controls.hd = (params.hd == 1#1))
    (pie : controls.pie = (params.pie == 1#1))
    (role : DescriptorRole) (slot : Nat) (before after : BitVec 64)
    (allowed : AllowedUpdate params role before after) (aligned : slot % 8 = 0)
    (present : S1ByteMemory.DescAt mem slot before) :
    PermissionImage rows params regs controls (S1ByteMemory.store mem slot after) := by
  intro row member
  obtain ⟨rowAligned, current, bytes, admitted⟩ := image row member
  refine ⟨rowAligned, ?_⟩
  by_cases same : slot = row.slot
  · subst slot
    have equal := S1ByteMemory.descriptor_unique mem row.slot current before bytes present
    subst current
    refine ⟨after, S1ByteMemory.stored_descriptor _ _ _, ?_⟩
    exact (canonical_admission_allowed_update params regs role before after allowed controls row.prior
      ha hd pie row.attributes row.access).mpr admitted
  · exact ⟨current, (S1ByteMemory.other_descriptor_iff mem slot row.slot after current aligned rowAligned same).mpr bytes,
      admitted⟩

theorem PermissionImage.program_write
    (image : PermissionImage rows params regs controls mem)
    (writes : Nat → Prop) (frame : WritesOnly writes (fun a => mem[a]?) (fun a => mem'[a]?))
    (separated : Separated (permissionRowsFootprint rows).byte writes) :
    PermissionImage rows params regs controls mem' := by
  intro row member
  obtain ⟨aligned, current, bytes, admitted⟩ := image row member
  refine ⟨aligned, current, ?_, admitted⟩
  intro i bound
  have covered : row.slot ∈ (permissionRowsFootprint rows).slots := List.mem_map.mpr ⟨row, member, rfl⟩
  have address := (permissionRowsFootprint rows).covers row.slot covered ⟨i, bound⟩
  exact (table_unchanged frame separated _ address).trans (bytes i bound)

/-- StoreHistory contains the ordered concrete writes from the source, not
    an assumed invariant-preservation answer. Endianness is the existing E3 LE
    instance; no statement about big-endian image realization is made here. -/
theorem StoreHistory.preserves_permission_image
    (history : StoreHistory params footprint before operations after)
    (endian : params.ee = 0#1)
    (ha : controls.ha = (params.ha == 1#1)) (hd : controls.hd = (params.hd == 1#1))
    (pie : controls.pie = (params.pie == 1#1))
    (image : PermissionImage rows params regs controls before) :
    PermissionImage rows params regs controls after := by
  induction history with
  | nil => exact image
  | cons step tail ih =>
    apply ih
    rw [step.le_stored endian]
    exact image.hardware_store ha hd pie _ _ _ _ step.allowed step.aligned (step.le_present endian)

/-- Only source-inspected attribute and access fields must agree at the native
    checker boundary. Shareability and other inactive data are not pinned. -/
theorem canonical_admission_data_congr (params : S1TTWParams) (regs : Regs)
    (view : S1LogicalReference.Permissions) (first second : AttributeBody)
    (left right : AccessDescriptor)
    (kind : first.kind = second.kind) (tags : first.tags = second.tags)
    (acctype : left.acctype = right.acctype) (read : left.read = right.read)
    (write : left.write = right.write) (tagaccess : left.tagaccess = right.tagaccess) :
    CanonicalAdmission params regs view first left ↔ CanonicalAdmission params regs view second right := by
  unfold CanonicalAdmission PermissionAdmissible permissionChecksPass
  simp only [kind, tags, acctype, read, write, tagaccess]

/-- Rebind an actual getter result by the fields inspected by admission.
    No equality of the complete parameter record or its inactive words is used. -/
theorem canonical_admission_params_congr (first second : S1TTWParams) (regs : Regs)
    (view : S1LogicalReference.Permissions) (attrs : AttributeBody) (input : AccessDescriptor)
    (ha : first.ha = second.ha) (hd : first.hd = second.hd)
    (pie : first.pie = second.pie) (wxn : first.wxn = second.wxn) :
    CanonicalAdmission first regs view attrs input ↔ CanonicalAdmission second regs view attrs input := by
  unfold CanonicalAdmission nativeAdmissionView el0AdmissionView admissionPermissionView
    nativePermissionProjection PermissionAdmissible permissionChecksPass computedControls baseControls directControls
  simp only [ha, hd, pie, wxn]

theorem PermissionImage.reparam (image : PermissionImage rows params regs controls mem)
    (actual : S1TTWParams) (ha : params.ha = actual.ha) (hd : params.hd = actual.hd)
    (pie : params.pie = actual.pie) (wxn : params.wxn = actual.wxn) :
    PermissionImage rows actual regs controls mem := by
  intro row member
  obtain ⟨aligned, d, bytes, admitted⟩ := image row member
  exact ⟨aligned, d, bytes, (canonical_admission_params_congr params actual regs _ _ _ ha hd pie wxn).mp admitted⟩

theorem computed_controls_register_congr (params : S1TTWParams) (left right : Regs)
    (enabled : e0OverlayEnabled left = e0OverlayEnabled right)
    (por : e0OverlayEnabled left = true → left.bank_BitVec_64 .POR_EL0 = right.bank_BitVec_64 .POR_EL0)
    (raw : ArmFull.Permissions) : computedControls raw params left = computedControls raw params right := by
  cases active : e0OverlayEnabled left with
  | false =>
    have inactive : e0OverlayEnabled right = false := enabled.symm.trans active
    simp [computedControls, finishControls, active, inactive]
  | true =>
    simp only [computedControls, enabled, currentOverlayRights, por active]

/-- Current active register data suffices. POR_EL0 remains free when EL0
    overlays are disabled; no complete register-bank equality is required. -/
theorem canonical_admission_register_congr (params : S1TTWParams) (left right : Regs)
    (enabled : e0OverlayEnabled left = e0OverlayEnabled right)
    (por : e0OverlayEnabled left = true → left.bank_BitVec_64 .POR_EL0 = right.bank_BitVec_64 .POR_EL0)
    (view : S1LogicalReference.Permissions) (attrs : AttributeBody) (input : AccessDescriptor) :
    CanonicalAdmission params left view attrs input ↔ CanonicalAdmission params right view attrs input := by
  unfold CanonicalAdmission
  simp only [enabled, computed_controls_register_congr params left right enabled por]

theorem PermissionImage.registers (image : PermissionImage rows params left controls mem)
    (right : Regs) (enabled : e0OverlayEnabled left = e0OverlayEnabled right)
    (por : e0OverlayEnabled left = true → left.bank_BitVec_64 .POR_EL0 = right.bank_BitVec_64 .POR_EL0) :
    PermissionImage rows params right controls mem := by
  intro row member
  obtain ⟨aligned, d, bytes, admitted⟩ := image row member
  exact ⟨aligned, d, bytes, (canonical_admission_register_congr params left right enabled por _ _ _).mp admitted⟩

theorem PermissionImage.guarded_page (image : PermissionImage rows params regs controls mem) (guarded : Bool) :
    PermissionImage rows params (gpRegs regs guarded) controls mem := image

#print axioms check_permission_image_sound
#print axioms PermissionImage.admission
#print axioms PermissionImage.hardware_store
#print axioms PermissionImage.program_write
#print axioms StoreHistory.preserves_permission_image
#print axioms canonical_admission_data_congr
#print axioms canonical_admission_params_congr
#print axioms PermissionImage.reparam
#print axioms canonical_admission_register_congr
#print axioms PermissionImage.registers
#print axioms PermissionImage.guarded_page
end ArmCert.Translate.Model
