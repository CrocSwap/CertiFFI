import ArmCertWalk.FinitePathLoop
import ArmCertTranslateModel.WalkAccess
import ArmCertTranslateModel.HostCurrentParams

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- Current bytes force a unique stable observation at each logical slot.
    This is derived from the existing image, not a new functional-observation
    premise. Duplicate rows and multiple descriptor roles remain permitted. -/
theorem topology_observation_consistent {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (state : State) (image : TopologyImageAt spec state)
    (logical : Nat) (firstPhysical secondPhysical : FullAddress)
    (firstView secondView : S1DescriptorPIE.View 64)
    (first : logicalObserve spec.logicalRows logical firstPhysical firstView)
    (second : logicalObserve spec.logicalRows logical secondPhysical secondView) :
    firstPhysical = secondPhysical ∧ firstView = secondView := by
  have firstIdentity := spec.identity logical firstPhysical firstView first
  have secondIdentity := spec.identity logical secondPhysical secondView second
  have address : firstPhysical.address = secondPhysical.address :=
    BitVec.eq_of_toNat_eq (firstIdentity.1.symm.trans secondIdentity.1)
  have space : firstPhysical.paspace = secondPhysical.paspace := firstIdentity.2.trans secondIdentity.2.symm
  have physical : firstPhysical = secondPhysical := by cases firstPhysical; cases secondPhysical; congr <;> assumption
  subst secondPhysical
  obtain ⟨firstRole, firstUsed⟩ := spec.represented logical firstPhysical firstView first
  obtain ⟨secondRole, secondUsed⟩ := spec.represented logical firstPhysical secondView second
  obtain ⟨firstWord, firstBytes, firstMeaning, _⟩ := image _ firstRole firstView firstUsed
  obtain ⟨secondWord, secondBytes, secondMeaning, _⟩ := image _ secondRole secondView secondUsed
  have words := S1ByteMemory.descriptor_unique state.mem firstPhysical.address.toNat firstWord secondWord firstBytes secondBytes
  exact ⟨rfl, firstMeaning.symm.trans (words ▸ secondMeaning)⟩

/-- Annotation uniqueness uses observed current-view consistency. Path proofs
    are propositions, so their proof identity alone cannot establish this. -/
theorem path_permission_annotation_unique
    {observe : S1LogicalReference.Observation} {paBits : Nat} {va : BitVec 64}
    {controls : S1LogicalReference.Controls} {level bits : Nat} {base : BitVec 48}
    {endpoint : S1LogicalReference.PathEnd}
    {path : S1LogicalReference.Path observe paBits va level bits base endpoint}
    {prior firstFinal secondFinal : S1LogicalReference.TablePermissions}
    {firstWords secondWords : List (BitVec 64)}
    (consistent : ∀ logical p q v w, observe logical p v → observe logical q w → v = w)
    (first : PathPermissionAnnotation observe paBits va controls path prior firstWords firstFinal)
    (second : PathPermissionAnnotation observe paBits va controls path prior secondWords secondFinal) :
    firstWords = secondWords ∧ firstFinal = secondFinal := by
  induction first generalizing secondWords secondFinal with
  | invalid level bits base physical view hl aligned present kind prior =>
    cases second with
    | invalid => exact ⟨rfl, rfl⟩
    | table _ _ _ _ otherView _ _ _ otherPresent otherKind _ _ _ _ _ _ =>
      have equal := consistent _ _ _ _ _ present otherPresent
      rw [← equal, kind] at otherKind
      contradiction
  | leaf level bits base physical view hl aligned present kind prior =>
    cases second with
    | leaf => exact ⟨rfl, rfl⟩
    | table _ _ _ _ otherView _ _ _ otherPresent otherKind _ _ _ _ _ _ =>
      have equal := consistent _ _ _ _ _ present otherPresent
      rw [← equal, kind] at otherKind
      contradiction
  | range level bits base physical view hl aligned present kind outOfRange prior =>
    cases second with
    | range => exact ⟨rfl, rfl⟩
    | table _ _ _ _ otherView _ _ _ otherPresent otherKind inRange _ _ _ _ _ =>
      have equal := consistent _ _ _ _ _ present otherPresent
      rw [← equal] at inRange
      omega
  | table level bits base physical view endpoint hl aligned present kind inRange tail prior final words annotation ih =>
    cases second with
    | invalid _ _ _ _ otherView _ _ otherPresent otherKind _ =>
      have equal := consistent _ _ _ _ _ present otherPresent
      rw [← equal, kind] at otherKind
      contradiction
    | leaf _ _ _ _ otherView _ _ otherPresent otherKind _ =>
      have equal := consistent _ _ _ _ _ present otherPresent
      rw [← equal, kind] at otherKind
      contradiction
    | range _ _ _ _ otherView _ _ otherPresent otherKind outOfRange _ =>
      have equal := consistent _ _ _ _ _ present otherPresent
      rw [← equal] at outOfRange
      omega
    | table _ _ _ _ otherView _ _ _ otherPresent otherKind _ _ _ _ _ other =>
      have equal := consistent _ _ _ _ _ present otherPresent
      subst otherView
      obtain ⟨wordEq, finalEq⟩ := ih other
      exact ⟨congrArg (view.stable :: ·) wordEq, finalEq⟩

/-- Static permission-row use for an existing successful path. All fields are
    row membership, finite checks or descriptor/path data. The actual walk
    constructs its own annotation; uniqueness above joins the two. -/
structure PathPermissionUse {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (query : AccessQuery)
    {level bits : Nat} {base : BitVec 48} {leafLevel logical : Nat}
    {physical : FullAddress} {view : S1DescriptorPIE.View 64}
    (path : S1LogicalReference.Path (logicalObserve spec.logicalRows)
      (effectiveBits spec.physicalConfig).toNat query.va level bits base
      (.leaf leafLevel logical physical view))
    (initialPrior : S1LogicalReference.TablePermissions) where
  row : PermissionRow
  member : row ∈ rows
  slot : row.slot = physical.address.toNat
  words : List (BitVec 64)
  annotation : PathPermissionAnnotation (logicalObserve spec.logicalRows)
    (effectiveBits spec.physicalConfig).toNat query.va spec.controls path initialPrior words row.prior
  used : rowsObserve spec.imageRows physical.address.toNat true view
  rowView : S1DescriptorPIE.view (spec.params.pie == 1#1) (spec.params.ha == 1#1)
    (spec.params.hd == 1#1) row.raw = view
  attributes : checkPermissionRowAttributes config spec.params row = true
  kind : row.access.acctype = query.request.raw.acctype
  read : row.access.read = query.request.raw.read
  write : row.access.write = query.request.raw.write
  tagaccess : row.access.tagaccess = query.request.raw.tagaccess


section PathUse
variable {domain : QueryDomain} {spec : TopologyImageSpec domain} {config : AttributeConfig}
  {rows : List PermissionRow} {query : AccessQuery} {level bits : Nat} {base : BitVec 48}
  {leafLevel logical : Nat} {physical : FullAddress} {view : S1DescriptorPIE.View 64}
  {path : S1LogicalReference.Path (logicalObserve spec.logicalRows)
    (effectiveBits spec.physicalConfig).toNat query.va level bits base
    (.leaf leafLevel logical physical view)} {initialPrior : S1LogicalReference.TablePermissions}

/-- Rebind static row-use data to the actual getter's active scalars. No
    equality of inactive parameter fields or source executions is required. -/
def PathPermissionUse.reparam
    (binding : PathPermissionUse spec config rows query path initialPrior)
    (actual : S1TTWParams) (active : ImageParamsEq spec.params actual) :
    PathPermissionUse {spec with params := actual} config rows query path initialPrior := by
  refine ⟨binding.row, binding.member, binding.slot, binding.words, binding.annotation,
    binding.used, ?_, ?_, binding.kind, binding.read, binding.write, binding.tagaccess⟩
  · simpa only [active.pie, active.ha, active.hd] using binding.rowView
  · simpa only [checkPermissionRowAttributes, active.mtx] using binding.attributes

theorem PathPermissionUse.final_prior
    (binding : PathPermissionUse spec config rows query path initialPrior)
    (state : State) (image : TopologyImageAt spec state)
    {words : List (BitVec 64)} {prior : S1LogicalReference.TablePermissions}
    (actual : PathPermissionAnnotation (logicalObserve spec.logicalRows)
      (effectiveBits spec.physicalConfig).toNat query.va spec.controls path initialPrior words prior) :
    binding.row.prior = prior :=
  (path_permission_annotation_unique
    (fun a p q v w first second => (topology_observation_consistent spec state image a p q v w first second).2)
    binding.annotation actual).2

theorem PathPermissionUse.endpoint_admission
    (binding : PathPermissionUse spec config rows query path initialPrior)
    (initial state : State) (registers : state.regs = initial.regs)
    (images : CurrentImagesAt spec config rows state)
    {words : List (BitVec 64)} {prior : S1LogicalReference.TablePermissions} {out : WalkVars}
    (actual : PathPermissionAnnotation (logicalObserve spec.logicalRows)
      (effectiveBits spec.physicalConfig).toNat query.va spec.controls path initialPrior words prior)
    (endpoint : WalkLeafEndpoint spec.params config spec.controls (outputOverlayEnabled initial.regs)
      leafLevel physical view prior out state) :
    PermissionAdmissible (walkCurrent out).permissions spec.params
      (attributeProjection (walkCurrent out).memattrs) query.request.raw
      (computedControls (walkCurrent out).permissions spec.params state.regs) ∧
    (walkCurrent out).memattrs.memtype = .MemType_Normal ∧
    (walkCurrent out).memattrs.inner.attrs = MemAttr_WB ∧
    (walkCurrent out).memattrs.outer.attrs = MemAttr_WB := by
  have priorEq := binding.final_prior state images.topology actual
  have used : rowsObserve spec.imageRows binding.row.slot true view := by rw [binding.slot]; exact binding.used
  exact walk_endpoint_image_admission spec config rows state initial.regs registers leafLevel physical view
    prior out endpoint images binding.row binding.member binding.slot priorEq used binding.rowView binding.attributes
    query.request.raw binding.kind binding.read binding.write binding.tagaccess
end PathUse

/-- Actual finite source loop, preserved current images and permission admission
    for its exact result. The only row/path join is static data. This is still
    the loop component: native prefix/suffix and M0581 compose separately. -/
theorem finite_path_loop_image_total {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (query : AccessQuery) (startlevel : Int)
    {level bits : Nat} {base : BitVec 48} {leafLevel logical : Nat}
    {physical : FullAddress} {view : S1DescriptorPIE.View 64}
    (path : S1LogicalReference.Path (logicalObserve spec.logicalRows)
      (effectiveBits spec.physicalConfig).toNat query.va level bits base
      (.leaf leafLevel logical physical view))
    (current : TTWState) (descaddr : FullAddress) (oldDescriptor : BitVec 64)
    (typ : DescriptorType) (fault : FaultRecord) (a64 s2 : Bool) (skl : BitVec 2)
    (walkaddr : AddressDescriptor) (initial : State)
    (binding : PathPermissionUse spec config rows query path (nativeTablePermissionProjection current.permissions))
    (format : WalkFormat spec.params spec.physicalConfig spec.controls)
    (callees : WalkCalleesAt spec.params spec.physicalConfig spec.controls config initial)
    (images : CurrentImagesAt spec config rows initial)
    (ss : query.request.raw.ss = .SS_NonSecure) (noFault : fault.statuscode = .Fault_None)
    (nonsecure : current.baseaddress.paspace = .PAS_NonSecure)
    (currentLevel : current.level = (level : Int)) (currentDisCH : current.disch = 0#1)
    (slot : descaddr.address.toNat = S1LogicalReference.entryAddress base query.va level bits)
    (space : descaddr.paspace = .PAS_NonSecure) :
    ∃ (steps : Nat) (out : WalkVars) (other : State) (words : List (BitVec 64))
      (prior : S1LogicalReference.TablePermissions) (operations : List TableUpdate),
      0 < steps ∧ steps ≤ 4 - level ∧
      S1WalkSource.named.loop0 spec.params query.va .Regime_EL20 query.request.raw 64 a64
        query.request.aligned fault current startlevel oldDescriptor skl walkaddr s2 typ descaddr initial =
        .ok (.ok out) other ∧
      PathPermissionAnnotation (logicalObserve spec.logicalRows) (effectiveBits spec.physicalConfig).toNat
        query.va spec.controls path (nativeTablePermissionProjection current.permissions) words prior ∧
      WalkLeafEndpoint spec.params config spec.controls (outputOverlayEnabled initial.regs)
        leafLevel physical view prior out other ∧
      other.regs = initial.regs ∧
      StoreHistory spec.params (rowsFootprint spec.imageRows) initial.mem operations other.mem ∧
      CurrentImagesAt spec config rows other ∧
      PermissionAdmissible (walkCurrent out).permissions spec.params
        (attributeProjection (walkCurrent out).memattrs) query.request.raw
        (computedControls (walkCurrent out).permissions spec.params other.regs) ∧
      (walkCurrent out).memattrs.memtype = .MemType_Normal ∧
      (walkCurrent out).memattrs.inner.attrs = MemAttr_WB ∧
      (walkCurrent out).memattrs.outer.attrs = MemAttr_WB := by
  obtain ⟨steps, out, other, words, prior, operations, positive, bounded, call, annotation,
    endpoint, registers, history⟩ := finite_path_loop_total spec config query.va query.request.raw startlevel
      path leafLevel logical physical view rfl binding.used current query.request.aligned descaddr oldDescriptor
      typ fault a64 s2 skl walkaddr initial format callees images.topology images.attributes ss noFault nonsecure
      currentLevel currentDisCH slot space
  have afterImages := images.store_history history registers format.endian callees.permissions.ha
    callees.permissions.hd callees.permissions.pie
  have admitted := binding.endpoint_admission initial other registers afterImages annotation endpoint
  exact ⟨steps, out, other, words, prior, operations, positive, bounded, call, annotation,
    endpoint, registers, history, afterImages, admitted⟩

#print axioms PathPermissionUse.reparam
#print axioms PathPermissionUse.final_prior
#print axioms PathPermissionUse.endpoint_admission
#print axioms finite_path_loop_image_total

#print axioms topology_observation_consistent
#print axioms path_permission_annotation_unique
end ArmCert.Translate.Model
