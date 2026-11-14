import ArmCertWalk.NativeWalkTotal
import ArmCertTranslateModel.PathPermissionBinding
import ArmCertTranslateModel.LeafOutputBinding

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- Facts about the exact native walk result. The canonical OUTPUT address is
    computed from its actual TTWState; its returned walkaddr still describes
    the descriptor access and is not asserted to be the translated data PA. -/
def WalkResultAdmitted (params : S1TTWParams) (mapping : BitVec 64 → Option Nat)
    (regs : Regs) (query : AccessQuery) (level : Nat)
    (result : FaultRecord × AddressDescriptor × TTWState × BitVec 64) : Prop :=
  result.1.statuscode = .Fault_None ∧
  PermissionAdmissible result.2.2.1.permissions params (attributeProjection result.2.2.1.memattrs)
    query.request.raw (computedControls result.2.2.1.permissions params regs) ∧
  result.2.2.1.memattrs.memtype = .MemType_Normal ∧
  result.2.2.1.memattrs.inner.attrs = MemAttr_WB ∧ result.2.2.1.memattrs.outer.attrs = MemAttr_WB ∧
  mapping query.va = some (S1LogicalReference.outputAddress query.va level result.2.2.1.baseaddress
    (result.2.2.1.contiguous == 1#1)).address.toNat ∧ AFReady params .leaf result.2.2.2

/-- Bind the COMPLETE actual native walker to current structural images,
    the declared partial map, and effective access admission. The actual
    native result/history are retained. M0581 leaf AF/dirty/Translate and
    certified-run preservation are separate remaining source compositions. -/
theorem native_walk_image_total {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (query : AccessQuery) (member : domain query)
    (leafLevel logical : Nat) (physical : FullAddress) (view : S1DescriptorPIE.View 64)
    (path : S1LogicalReference.Path (logicalObserve spec.logicalRows)
      (effectiveBits spec.physicalConfig).toNat query.va spec.layout.start
      (S1LogicalReference.rootBits spec.layout.start spec.layout.inputBits) spec.layout.root
      (.leaf leafLevel logical physical view))
    (binding : PathPermissionUse spec config rows query path ⟨0#2, false, false⟩)
    (fault : FaultRecord) (initial : State)
    (format : WalkFormat spec.params spec.physicalConfig spec.controls)
    (callees : WalkCalleesAt spec.params spec.physicalConfig spec.controls config initial)
    (images : CurrentImagesAt spec config rows initial)
    (layout : CurrentLayoutAt spec.layout spec.params query.va initial.regs)
    (disch : spec.params.disch = 0#1)
    (ss : query.request.raw.ss = .SS_NonSecure) (noFault : fault.statuscode = .Fault_None)
    (cache : initial.regs.bank_Bool .__tlb_enabled = false)
    (epd : currentWalkEPD initial.regs query.va = 0#1)
    (map : LeafMapAt mapping spec.physicalConfig initial.regs query leafLevel view) :
    ∃ result other,
      AArch64_S1Walk fault spec.params query.va .Regime_EL20 query.request.raw 64 initial = .ok result other ∧
      CleanWalkResult spec config query leafLevel logical physical view path initial result other ∧
      CurrentImagesAt spec config rows other ∧
      WalkResultAdmitted spec.params mapping other.regs query leafLevel result := by
  obtain ⟨result, other, call, clean⟩ := native_walk_total spec config query member leafLevel logical physical view
    path binding.used fault initial format callees images.topology images.attributes layout disch ss noFault cache epd
    map.admissible
  obtain ⟨steps, out, words, prior, operations, positive, bounded, resultEq, annotation,
    endpoint, registers, history⟩ := clean
  have afterImages := images.store_history history registers format.endian callees.permissions.ha
    callees.permissions.hd callees.permissions.pie
  have admitted := binding.endpoint_admission initial other registers afterImages annotation endpoint
  have afterMap : LeafMapAt mapping spec.physicalConfig other.regs query leafLevel view := by
    rw [registers]; exact map
  have output := walk_endpoint_output_inputs spec config mapping other query leafLevel physical view prior out
    (outputOverlayEnabled initial.regs) endpoint afterImages.topology binding.used afterMap
  have faultNone : (walkFault out).statuscode = .Fault_None := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, actualFault, _⟩ := endpoint
    exact actualFault
  refine ⟨result, other, call, ?_, afterImages, ?_⟩
  · exact ⟨steps, out, words, prior, operations, positive, bounded, resultEq, annotation,
      endpoint, registers, history⟩
  · rw [resultEq]
    exact ⟨faultNone, admitted.1, admitted.2.1, admitted.2.2.1, admitted.2.2.2, output.1, output.2.2.2.1⟩

#print axioms native_walk_image_total
end ArmCert.Translate.Model
