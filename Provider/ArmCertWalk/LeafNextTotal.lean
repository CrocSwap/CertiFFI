import ArmCertWalk.LeafPrefixTotal
import ArmCertWalk.LeafAfterTotal

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

structure LeafMeaning (config : AttributeConfig) (controls : S1LogicalReference.Controls)
    (params : S1TTWParams) (overlay : Bool) (current : TTWState) (level : Nat)
    (descriptor : BitVec 64) (next : TTWState) : Prop where
  istable : next.istable = false
  level_eq : next.level = (level : Int)
  base : next.baseaddress.address = S1LogicalReference.leafBase level descriptor
  nonsecure : next.baseaddress.paspace = .PAS_NonSecure
  attrs : AttributeInterprets (selectedAttribute config descriptor) (leafShareability descriptor)
    params next.memattrs
  permissions : nativePermissionProjection params overlay next.permissions =
    descriptorPermissionView controls (nativeTablePermissionProjection current.permissions) descriptor
  assured : next.s1assured = false
  contiguous : next.contiguous =
    if current.disch == 1#1 then 0#1 else BitVec.ofBool (descriptor.getLsbD 52)
  nG : next.nG = BitVec.ofBool (descriptor.getLsbD 11)
  guarded : next.guardedpage = BitVec.ofBool (descriptor.getLsbD 50)

/-- The actual source leaf call, including its actual choices and successive
callee states. Inactive undefined fields remain those of the actual source seed. -/
theorem leaf_next_canonical_total (config : AttributeConfig) (controls : S1LogicalReference.Controls)
    (current : TTWState) (level : Nat) (s2 : Bool) (params : S1TTWParams)
    (descriptor : BitVec 64) (state : State)
    (nonsecure : current.baseaddress.paspace = .PAS_NonSecure)
    (currentLevel : current.level = (level : Int)) (positive : 1 ≤ level) (valid : level ≤ 3)
    (aie : params.aie = 0#1) (d128 : params.d128 = 0#1) (ds : params.ds = 0#1)
    (pnch : params.pnch = 0#1) (tg : params.tgx = .TGx_4KB)
    (activeAttrs : ActiveAttributesAt config params state)
    (admissible : AttributeAdmissible config (selectedAttribute config descriptor))
    (binding : LeafPermissionControls params (outputOverlayEnabled state.regs) controls) :
    ∃ next other,
      AArch64_S1NextWalkStateLeaf current s2 .Regime_EL20 .SS_NonSecure params descriptor state =
        .ok next other ∧
      LeafMeaning config controls params (outputOverlayEnabled state.regs) current level descriptor next ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  obtain ⟨prepared, first, prepareCall, prepareMeaning, prepareRegs, prepareMem, prepareEvents⟩ :=
    leaf_prefix_total current level s2 params descriptor state nonsecure currentLevel valid aie d128 ds tg
  obtain ⟨attrs, second, attributeCall, attributeMeaning, attributeRegs, attributeMem, attributeEvents⟩ :=
    selected_attribute_total config params first (activeAttrs.of_regs prepareRegs)
      descriptor (leafShareability descriptor) admissible
  have stagedAttribute : LeafNextStages.attributes params (leafAttributeIndex descriptor)
      (leafShareability descriptor) first = .ok attrs second := by
    simpa only [LeafNextStages.attributes, leaf_index_canonical, bind_pure] using attributeCall
  have afterBinding : LeafPermissionControls params (outputOverlayEnabled second.regs) controls := by
    rw [attributeRegs, prepareRegs]
    exact binding
  obtain ⟨permissions, other, afterCall, permissionMeaning, afterRegs, afterMem, afterEvents⟩ :=
    leaf_after_total current s2 params descriptor prepared attrs controls second d128 pnch tg
      (by omega) (by omega) afterBinding
  refine ⟨leafFinished current {prepared with memattrs := attrs} permissions descriptor, other, ?_, ?_, afterRegs.trans (attributeRegs.trans prepareRegs),
    afterMem.trans (attributeMem.trans prepareMem), afterEvents.trans (attributeEvents.trans prepareEvents)⟩
  · rw [LeafNextSource.source_eq, LeafNextStages.action_eq]
    simp only [LeafNextStages.staged, Bind.bind, EStateM.bind, prepareCall, stagedAttribute, afterCall]
  · refine ⟨prepareMeaning.istable, prepareMeaning.level_eq, prepareMeaning.base,
      prepareMeaning.nonsecure, attributeMeaning, ?_, rfl, rfl, rfl, rfl⟩
    simpa only [leafFinished, attributeRegs, prepareRegs] using permissionMeaning

#print axioms leaf_next_canonical_total
end ArmCertWalk
