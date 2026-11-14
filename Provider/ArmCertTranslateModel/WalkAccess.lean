import ArmCertWalk.WalkEndpoint
import ArmCertTranslateModel.CurrentImages

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

/-- Join an EXISTING actual finite-walk endpoint to the image/permission row.
    There is no new leaf execution and no equality to a rerun's undefined seed.
    Slot/prior/view/access links are current static certificate data; the source
    finite-walk theorem constructs endpoint and sameRegs internally. -/
theorem walk_endpoint_image_admission {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (state : State) (sourceRegs : Regs)
    (sameRegs : state.regs = sourceRegs) (level : Nat) (physical : FullAddress)
    (view : S1DescriptorPIE.View 64) (prior : S1LogicalReference.TablePermissions) (out : WalkVars)
    (endpoint : WalkLeafEndpoint spec.params config spec.controls (outputOverlayEnabled sourceRegs)
      level physical view prior out state)
    (images : CurrentImagesAt spec config rows state)
    (row : PermissionRow) (member : row ∈ rows) (slot : row.slot = physical.address.toNat)
    (rowPrior : row.prior = prior) (used : rowsObserve spec.imageRows row.slot true view)
    (rowView : S1DescriptorPIE.view (spec.params.pie == 1#1) (spec.params.ha == 1#1)
      (spec.params.hd == 1#1) row.raw = view)
    (attributes : checkPermissionRowAttributes config spec.params row = true)
    (input : AccessDescriptor) (kind : row.access.acctype = input.acctype)
    (read : row.access.read = input.read) (write : row.access.write = input.write)
    (tagaccess : row.access.tagaccess = input.tagaccess) :
    PermissionAdmissible (walkCurrent out).permissions spec.params
      (attributeProjection (walkCurrent out).memattrs) input
      (computedControls (walkCurrent out).permissions spec.params state.regs) ∧
    (walkCurrent out).memattrs.memtype = .MemType_Normal ∧
    (walkCurrent out).memattrs.inner.attrs = MemAttr_WB ∧
    (walkCurrent out).memattrs.outer.attrs = MemAttr_WB := by
  obtain ⟨current, descriptor, levelEq, disch, actualPrior, descriptorView, present,
    descriptorEq, slotEq, stop, noFault, meaning⟩ := endpoint
  have bytes : S1ByteMemory.DescAt state.mem row.slot descriptor := by simpa only [slot] using present
  obtain ⟨admitted, normal, inner, outer⟩ := leaf_meaning_image_admission rows (rowsObserve spec.imageRows)
    config spec.params spec.controls sourceRegs state sameRegs current level descriptor (walkCurrent out)
    meaning row member view bytes used descriptorView rowView (rowPrior.trans actualPrior.symm)
    attributes images.permissions images.writeback
  exact ⟨(permission_admissible_access_congr _ _ _ _ _ _ kind read write tagaccess).mp admitted,
    normal, inner, outer⟩

/-- Actual permission-check success at the supplied actual endpoint state.
    This does not assert that M0581 calls the checker immediately after loop0;
    its intervening checks/AF/dirty updates still require source composition. -/
theorem walk_endpoint_permission_check_total {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (state : State) (sourceRegs : Regs)
    (sameRegs : state.regs = sourceRegs) (level : Nat) (physical : FullAddress)
    (view : S1DescriptorPIE.View 64) (prior : S1LogicalReference.TablePermissions) (out : WalkVars)
    (endpoint : WalkLeafEndpoint spec.params config spec.controls (outputOverlayEnabled sourceRegs)
      level physical view prior out state)
    (images : CurrentImagesAt spec config rows state)
    (row : PermissionRow) (member : row ∈ rows) (slot : row.slot = physical.address.toNat)
    (rowPrior : row.prior = prior) (used : rowsObserve spec.imageRows row.slot true view)
    (rowView : S1DescriptorPIE.view (spec.params.pie == 1#1) (spec.params.ha == 1#1)
      (spec.params.hd == 1#1) row.raw = view)
    (attributes : checkPermissionRowAttributes config spec.params row = true)
    (input : AccessDescriptor) (kind : row.access.acctype = input.acctype)
    (read : row.access.read = input.read) (write : row.access.write = input.write)
    (tagaccess : row.access.tagaccess = input.tagaccess)
    (el : input.el = EL0) (security : input.ss = .SS_NonSecure) :
    ∃ afterCheck,
      AArch64_S1CheckPermissions (walkFault out) .Regime_EL20 (walkCurrent out) spec.params input state =
        .ok (walkFault out) afterCheck ∧
      (walkFault out).statuscode = .Fault_None ∧
      afterCheck.regs = state.regs ∧ afterCheck.mem = state.mem ∧ afterCheck.events = state.events := by
  have admitted := (walk_endpoint_image_admission spec config rows state sourceRegs sameRegs level physical view
    prior out endpoint images row member slot rowPrior used rowView attributes input kind read write tagaccess).1
  obtain ⟨afterCheck, call, registers, memory, events⟩ := permission_check_total (walkFault out) (walkCurrent out)
    spec.params input state el security admitted
  obtain ⟨_, _, _, _, _, _, _, _, _, _, noFault, _⟩ := endpoint
  exact ⟨afterCheck, call, noFault, registers, memory, events⟩

#print axioms walk_endpoint_image_admission
#print axioms walk_endpoint_permission_check_total
end ArmCert.Translate.Model
