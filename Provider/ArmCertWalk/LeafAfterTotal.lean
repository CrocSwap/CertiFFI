import ArmCertWalk.LeafFinishFacts

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

theorem leaf_after_total (current : TTWState) (s2 : Bool) (params : S1TTWParams)
    (descriptor : BitVec 64) (prepared : TTWState) (attrs : MemoryAttributes)
    (controls : S1LogicalReference.Controls) (state : State)
    (d128 : params.d128 = 0#1) (pnch : params.pnch = 0#1) (tg : params.tgx = .TGx_4KB)
    (positive : 1 ≤ current.level) (level : current.level ≤ 3)
    (binding : LeafPermissionControls params (outputOverlayEnabled state.regs) controls) :
    ∃ permissions other,
      LeafNextStages.afterAttrs current s2 params descriptor prepared attrs state =
        .ok (leafFinished current {prepared with memattrs := attrs} permissions descriptor) other ∧
      nativePermissionProjection params (outputOverlayEnabled state.regs) permissions =
        descriptorPermissionView controls (nativeTablePermissionProjection current.permissions) descriptor ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  obtain ⟨permissions, first, permissionCall, permissionView, permissionRegs, permissionMem, permissionEvents⟩ :=
    output_permissions_canonical_total current.permissions descriptor params controls state d128 binding
  obtain ⟨other, finishCall, finishRegs, finishMem, finishEvents⟩ :=
    leaf_finish_total current s2 params descriptor {prepared with memattrs := attrs} permissions first
      d128 pnch tg positive level
  refine ⟨permissions, other, ?_, permissionView, finishRegs.trans permissionRegs,
    finishMem.trans permissionMem, finishEvents.trans permissionEvents⟩
  rw [LeafNextStages.after_attrs_eq]
  simp only [Bind.bind, EStateM.bind, permissionCall, finishCall]

#print axioms leaf_after_total
end ArmCertWalk
