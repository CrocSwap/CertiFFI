import ArmCertTranslateModel.CurrentBinding
import ArmCertTranslateModel.WriteBackBinding
import ArmCertWalk.LeafNextTotal

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

/-- The exact attribute observations inspected by the source permission policy.
    Cache hints, transient values, device subtype and inactive tags are free. -/
def permissionAttributeKey (attrs : AttributeBody) : Bool × Bool :=
  (normalAttributeKind attrs.kind, attrs.tags == .MemTag_CanonicallyTagged)

theorem canonical_admission_attribute_key_congr (params : S1TTWParams) (regs : Regs)
    (view : S1LogicalReference.Permissions) (first second : AttributeBody) (input : AccessDescriptor)
    (key : permissionAttributeKey first = permissionAttributeKey second) :
    CanonicalAdmission params regs view first input ↔ CanonicalAdmission params regs view second input := by
  have normal := congrArg Prod.fst key
  have tagged := congrArg Prod.snd key
  change normalAttributeKind first.kind = normalAttributeKind second.kind at normal
  change (first.tags == .MemTag_CanonicallyTagged) = (second.tags == .MemTag_CanonicallyTagged) at tagged
  unfold CanonicalAdmission PermissionAdmissible permissionChecksPass
  simp only [normal, tagged]

theorem permission_admissible_access_congr (raw : ArmFull.Permissions) (params : S1TTWParams)
    (attrs : AttributeBody) (regs : Regs) (first second : AccessDescriptor)
    (kind : first.acctype = second.acctype) (read : first.read = second.read)
    (write : first.write = second.write) (tagaccess : first.tagaccess = second.tagaccess) :
    PermissionAdmissible raw params attrs first (computedControls raw params regs) ↔
      PermissionAdmissible raw params attrs second (computedControls raw params regs) := by
  unfold PermissionAdmissible permissionChecksPass
  simp only [kind, read, write, tagaccess]

/-- Attribute selection uses stable bits2..4 of the existing descriptor view.
    This reuses the selectedAttribute function; it defines no decoder or walk. -/
theorem selected_attribute_view_congr (config : AttributeConfig) (pie ha hd : Bool)
    (first second : BitVec 64) (view : S1DescriptorPIE.view pie ha hd first = S1DescriptorPIE.view pie ha hd second) :
    selectedAttribute config first = selectedAttribute config second := by
  have bit2 := congrArg (fun v => v.stable.getLsbD 2) view
  have bit3 := congrArg (fun v => v.stable.getLsbD 3) view
  have bit4 := congrArg (fun v => v.stable.getLsbD 4) view
  simp only [S1DescriptorPIE.view, S1Descriptor.stable] at bit2 bit3 bit4
  simp at bit2 bit3 bit4
  have slice : first.extractLsb' 2 3 = second.extractLsb' 2 3 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i bound
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    all_goals simp [bit2, bit3, bit4]
  have index : descriptorIndex first = descriptorIndex second := by
    apply Fin.ext
    change (first.extractLsb' 2 3).toNat = (second.extractLsb' 2 3).toNat
    rw [slice]
  simp only [selectedAttribute, index]

def checkPermissionRowAttributes (config : AttributeConfig) (params : S1TTWParams) (row : PermissionRow) : Bool :=
  decide (permissionAttributeKey row.attributes =
    permissionAttributeKey (decodedAttributeBody (selectedAttribute config row.raw) params.mtx))

theorem descriptor_leaf_bounds (level : Nat) (descriptor : BitVec 64)
    (leaf : S1LogicalReference.descriptorKind level descriptor = .ok .leaf) : 1 ≤ level ∧ level ≤ 3 := by
  have valid : level ≤ 3 := by
    by_cases inside : level ≤ 3
    · exact inside
    · have large : level > 3 := by omega
      simp [S1LogicalReference.descriptorKind, large] at leaf
  refine ⟨?_, valid⟩
  by_cases positive : 1 ≤ level
  · exact positive
  · have zero : level = 0 := by omega
    subst level
    cases bit0 : descriptor[0] <;> cases bit1 : descriptor[1] <;>
      simp [S1LogicalReference.descriptorKind, bit0, bit1] at leaf

/-- Pure join for THAT already-returned native leaf. It consumes the source
    endpoint's current data and never calls or reruns the leaf helper. -/
theorem leaf_meaning_image_admission (rows : List PermissionRow) (observe : RoleObservation)
    (config : AttributeConfig) (params : S1TTWParams) (controls : S1LogicalReference.Controls)
    (sourceRegs : Regs) (state : State) (sameRegs : state.regs = sourceRegs)
    (current : TTWState) (level : Nat) (descriptor : BitVec 64) (next : TTWState)
    (meaning : LeafMeaning config controls params (outputOverlayEnabled sourceRegs) current level descriptor next)
    (row : PermissionRow) (member : row ∈ rows) (view : S1DescriptorPIE.View 64)
    (present : S1ByteMemory.DescAt state.mem row.slot descriptor) (used : observe row.slot true view)
    (descriptorView : S1DescriptorPIE.view (params.pie == 1#1) (params.ha == 1#1)
      (params.hd == 1#1) descriptor = view)
    (rowView : S1DescriptorPIE.view (params.pie == 1#1) (params.ha == 1#1) (params.hd == 1#1) row.raw = view)
    (prior : row.prior = nativeTablePermissionProjection current.permissions)
    (attributes : checkPermissionRowAttributes config params row = true)
    (permissions : PermissionImage rows params state.regs controls state.mem)
    (wb : WriteBackAttributeImage observe config state.mem) :
    PermissionAdmissible next.permissions params (attributeProjection next.memattrs) row.access
      (computedControls next.permissions params state.regs) ∧
    next.memattrs.memtype = .MemType_Normal ∧ next.memattrs.inner.attrs = MemAttr_WB ∧
    next.memattrs.outer.attrs = MemAttr_WB := by
  have selected := selected_attribute_view_congr config _ _ _ descriptor row.raw (descriptorView.trans rowView.symm)
  have attributeKey : permissionAttributeKey row.attributes = permissionAttributeKey (attributeProjection next.memattrs) := by
    rw [meaning.attrs.1, selected]
    exact of_decide_eq_true attributes
  have admitted := (canonical_admission_attribute_key_congr params state.regs _ _ _ row.access attributeKey).mp
    (permissions.admission row member descriptor present)
  have projection : nativePermissionProjection params (outputOverlayEnabled state.regs) next.permissions =
      descriptorPermissionView controls row.prior descriptor := by
    simpa only [sameRegs, prior] using meaning.permissions
  have allowed : PermissionAdmissible next.permissions params (attributeProjection next.memattrs) row.access
      (computedControls next.permissions params state.regs) := by
    apply admitted next.permissions
    rw [native_admission_from_output, projection]
  exact ⟨allowed, interpreted_writeback _ _ _ _ meaning.attrs (wb row.slot view used descriptor present)⟩

/-- Bind an actual native leaf result to preserved current byte/attribute/
    permission images. Prior and row/view equations are current data linkage
    obligations of the existing Path, not callee-success or future answers.

    This proves the leaf helper result and current permission admissibility;
    it does not assert adjacency to the later permission-check call or complete
    the native walk/Translate. The caller threads its actual source states. -/
theorem leaf_image_total (rows : List PermissionRow) (observe : RoleObservation)
    (config : AttributeConfig) (params : S1TTWParams) (controls : S1LogicalReference.Controls)
    (state : State) (current : TTWState) (level : Nat) (s2 : Bool)
    (row : PermissionRow) (member : row ∈ rows) (view : S1DescriptorPIE.View 64) (descriptor : BitVec 64)
    (present : S1ByteMemory.DescAt state.mem row.slot descriptor) (used : observe row.slot true view)
    (descriptorView : S1DescriptorPIE.view (params.pie == 1#1) (params.ha == 1#1)
      (params.hd == 1#1) descriptor = view)
    (rowView : S1DescriptorPIE.view (params.pie == 1#1) (params.ha == 1#1) (params.hd == 1#1) row.raw = view)
    (kind : S1LogicalReference.descriptorKind level view.stable = .ok .leaf)
    (prior : row.prior = nativeTablePermissionProjection current.permissions)
    (attributes : checkPermissionRowAttributes config params row = true)
    (permissions : PermissionImage rows params state.regs controls state.mem)
    (valid : AttributeImage observe config state.mem) (wb : WriteBackAttributeImage observe config state.mem)
    (active : ActiveAttributesAt config params state)
    (format : HostLower.Shape tcr mair params)
    (nonsecure : current.baseaddress.paspace = .PAS_NonSecure) (currentLevel : current.level = (level : Int))
    (binding : LeafPermissionControls params (outputOverlayEnabled state.regs) controls) :
    ∃ next other,
      AArch64_S1NextWalkStateLeaf current s2 .Regime_EL20 .SS_NonSecure params descriptor state =
        .ok next other ∧
      LeafMeaning config controls params (outputOverlayEnabled state.regs) current level descriptor next ∧
      PermissionAdmissible next.permissions params (attributeProjection next.memattrs) row.access
        (computedControls next.permissions params other.regs) ∧
      next.memattrs.memtype = .MemType_Normal ∧ next.memattrs.inner.attrs = MemAttr_WB ∧
      next.memattrs.outer.attrs = MemAttr_WB ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  have bounds := descriptor_leaf_bounds level view.stable kind
  obtain ⟨tg, d128, aie, pnch, ds, _, _, _⟩ := format
  obtain ⟨next, other, call, meaning, registers, memory, events⟩ :=
    leaf_next_canonical_total config controls current level s2 params descriptor state nonsecure
      currentLevel bounds.1 bounds.2 aie d128 ds pnch tg active
      (valid row.slot view used descriptor present) binding
  obtain ⟨allowed, normal, inner, outer⟩ := leaf_meaning_image_admission rows observe config params controls
    state.regs state rfl current level descriptor next meaning row member view present used descriptorView rowView
    prior attributes permissions wb
  exact ⟨next, other, call, meaning, by simpa only [registers] using allowed,
    normal, inner, outer, registers, memory, events⟩

#print axioms canonical_admission_attribute_key_congr
#print axioms permission_admissible_access_congr
#print axioms selected_attribute_view_congr
#print axioms descriptor_leaf_bounds
#print axioms leaf_image_total
#print axioms leaf_meaning_image_admission
end ArmCert.Translate.Model
