import ArmCertTranslateModel.PermissionImage
import ArmCertTranslateModel.WriteBackBinding

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

def checkPermissionRowsCovered (rows : List PermissionRow) (footprint : Footprint) : Bool :=
  rows.all (fun row => decide (row.slot ∈ footprint.slots))

theorem check_permission_rows_covered_sound (rows : List PermissionRow) (footprint : Footprint)
    (checked : checkPermissionRowsCovered rows footprint = true) :
    ∀ row ∈ rows, row.slot ∈ footprint.slots := by
  intro row member
  exact of_decide_eq_true ((List.all_eq_true.mp checked) row member)

theorem permission_rows_byte_subset (rows : List PermissionRow) (footprint : Footprint)
    (width : footprint.width = 8) (covered : ∀ row ∈ rows, row.slot ∈ footprint.slots) :
    ∀ address, (permissionRowsFootprint rows).byte address → footprint.byte address := by
  rintro address ⟨slot, member, lower, upper⟩
  obtain ⟨row, rowMember, same⟩ := List.mem_map.mp member
  refine ⟨slot, ?_, lower, ?_⟩
  · rw [← same]
    exact covered row rowMember
  · simpa only [permissionRowsFootprint, width] using upper

/-- Current image components assembled for source callers. Every field is
    finite row coverage or current byte/admission data. There is no future
    call, source-success, event-equality or preservation-law field. This is an
    image component, not the complete mode/path/map/run contract. -/
structure CurrentImagesAt {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (state : State) : Prop where
  covered : ∀ row ∈ rows, row.slot ∈ (rowsFootprint spec.imageRows).slots
  topology : TopologyImageAt spec state
  attributes : AttributeImage (rowsObserve spec.imageRows) config state.mem
  writeback : WriteBackAttributeImage (rowsObserve spec.imageRows) config state.mem
  permissions : PermissionImage rows spec.params state.regs spec.controls state.mem

theorem check_current_images_sound {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (state : State)
    (coverage : checkPermissionRowsCovered rows (rowsFootprint spec.imageRows) = true)
    (bytes : checkImage spec.imageRows (spec.params.pie == 1#1) (spec.params.ha == 1#1)
      (spec.params.hd == 1#1) state.mem = true)
    (attributes : checkAttributeImage spec.imageRows config = true)
    (writeback : checkWriteBackAttributeImage spec.imageRows config = true)
    (permissions : checkPermissionImage rows spec.params state.regs spec.controls state.mem = true) :
    CurrentImagesAt spec config rows state :=
  ⟨check_permission_rows_covered_sound rows _ coverage, topology_check_initial spec state bytes,
    check_attribute_image_sound _ _ _ _ bytes attributes,
    check_writeback_attribute_image_sound _ _ _ _ bytes writeback,
    check_permission_image_sound _ _ _ _ _ permissions⟩

theorem CurrentImagesAt.frame (image : CurrentImagesAt spec config rows before)
    (registers : after.regs = before.regs) (memory : after.mem = before.mem) :
    CurrentImagesAt spec config rows after := by
  refine ⟨image.covered, ?_, ?_, ?_, ?_⟩
  · simpa only [TopologyImageAt, memory] using image.topology
  · simpa only [memory] using image.attributes
  · simpa only [memory] using image.writeback
  · simpa only [registers, memory] using image.permissions

/-- Apply a PAST ordered source-derived StoreHistory. This theorem does not
    assume a preservation callback for future source calls or a future run. -/
theorem CurrentImagesAt.store_history (image : CurrentImagesAt spec config rows before)
    (history : StoreHistory spec.params (rowsFootprint spec.imageRows) before.mem operations after.mem)
    (registers : after.regs = before.regs) (endian : spec.params.ee = 0#1)
    (ha : spec.controls.ha = (spec.params.ha == 1#1)) (hd : spec.controls.hd = (spec.params.hd == 1#1))
    (pie : spec.controls.pie = (spec.params.pie == 1#1)) : CurrentImagesAt spec config rows after := by
  refine ⟨image.covered, ?_, history.preserves_attributes endian spec.aligned image.attributes,
    history.preserves_writeback endian spec.aligned image.writeback, ?_⟩
  · exact history.preserves_image endian spec.aligned image.topology
  · rw [registers]
    exact history.preserves_permission_image endian ha hd pie image.permissions

theorem CurrentImagesAt.program_write (image : CurrentImagesAt spec config rows before)
    (writes : Nat → Prop) (frame : WritesOnly writes (fun a => before.mem[a]?) (fun a => after.mem[a]?))
    (separated : Separated (rowsFootprint spec.imageRows).byte writes)
    (enabled : e0OverlayEnabled before.regs = e0OverlayEnabled after.regs)
    (por : e0OverlayEnabled before.regs = true →
      before.regs.bank_BitVec_64 .POR_EL0 = after.regs.bank_BitVec_64 .POR_EL0) :
    CurrentImagesAt spec config rows after := by
  refine ⟨image.covered, topology_program_write spec before after image.topology writes frame separated,
    image.attributes.program_write (rowsFootprint spec.imageRows) rfl (rows_covered spec.imageRows) frame separated,
    image.writeback.program_write (rowsFootprint spec.imageRows) rfl (rows_covered spec.imageRows) frame separated, ?_⟩
  have rowSeparation : Separated (permissionRowsFootprint rows).byte writes := by
    intro address member
    exact separated address (permission_rows_byte_subset rows _ rfl image.covered address member)
  exact (image.permissions.program_write writes frame rowSeparation).registers after.regs enabled por

theorem CurrentImagesAt.guarded_page (image : CurrentImagesAt spec config rows state) (guarded : Bool) :
    CurrentImagesAt spec config rows {state with regs := gpRegs state.regs guarded} :=
  ⟨image.covered, image.topology, image.attributes, image.writeback, image.permissions.guarded_page guarded⟩

theorem CurrentImagesAt.reparam (image : CurrentImagesAt spec config rows state) (actual : S1TTWParams)
    (ha : spec.params.ha = actual.ha) (hd : spec.params.hd = actual.hd)
    (pie : spec.params.pie = actual.pie) (wxn : spec.params.wxn = actual.wxn) :
    CurrentImagesAt {spec with params := actual} config rows state :=
  ⟨image.covered, (topology_image_reparam spec state actual pie.symm ha.symm hd.symm).mpr image.topology,
    image.attributes, image.writeback, image.permissions.reparam actual ha hd pie wxn⟩

#print axioms check_current_images_sound
#print axioms CurrentImagesAt.frame
#print axioms CurrentImagesAt.store_history
#print axioms CurrentImagesAt.program_write
#print axioms CurrentImagesAt.guarded_page
#print axioms CurrentImagesAt.reparam
end ArmCert.Translate.Model
