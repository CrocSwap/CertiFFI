import ArmCertWalk.ComputedPermissionStages
import ArmCertWalk.ComputedPermissionMeaning
import ArmCertWalk.OverlayPermissionTotal

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

namespace ArmCertWalk

theorem after_base_permissions_total (ws : TTWState) (wp : S1TTWParams)
    (input : AccessDescriptor) (base : S1AccessControls) (state : State) :
    ∃ controls other, ComputedPermissionStages.afterBase ws wp input base state = .ok controls other ∧
      computedControlProjection controls = finishControls (baseControlProjection base)
        (e0OverlayEnabled state.regs) (currentOverlayRights ws.permissions state.regs) ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  obtain ⟨query, queryCall, queryRegs, queryMem, queryEvents⟩ :=
    e0_overlay_query_total wp.nv1 state
  cases enabled : e0OverlayEnabled state.regs with
  | false =>
    rw [enabled] at queryCall
    simp only [ComputedPermissionStages.afterBase, DirectPermissionSource.el0Nonsecure,
      EL0, BEq.rfl, bne_self_eq_false, ↓reduceIte, Bind.bind, EStateM.bind, queryCall,
      Pure.pure, EStateM.pure, Bool.not_false, Bool.false_eq_true]
    refine ⟨_, query, rfl, ?_, queryRegs, queryMem, queryEvents⟩
    by_cases wxn : base.wxn = 1#1 <;>
      simp [computedControlProjection, finishControls, baseControlProjection, wxn]
  | true =>
    rw [enabled] at queryCall
    cases active : base.overlay with
    | false =>
      simp only [ComputedPermissionStages.afterBase, DirectPermissionSource.el0Nonsecure,
        EL0, BEq.rfl, bne_self_eq_false, ↓reduceIte, Bind.bind, EStateM.bind, queryCall,
        Pure.pure, EStateM.pure, Bool.not_true, Bool.false_eq_true, active]
      refine ⟨_, query, rfl, ?_, queryRegs, queryMem, queryEvents⟩
      by_cases wxn : base.wxn = 1#1 <;>
        simp [computedControlProjection, finishControls, baseControlProjection, active, wxn]
    | true =>
      obtain ⟨overlay, other, overlayCall, overlayMeaning, overlayRegs, overlayMem, overlayEvents⟩ :=
        overlay_permissions_total ws (DirectPermissionSource.el0Nonsecure input) query
          rfl rfl
      dsimp only [DirectPermissionSource.el0Nonsecure, EL0] at overlayCall
      rw [queryRegs] at overlayMeaning
      simp only [ComputedPermissionStages.afterBase, DirectPermissionSource.el0Nonsecure,
        EL0, BEq.rfl, bne_self_eq_false, ↓reduceIte, Bind.bind, EStateM.bind, queryCall,
        Pure.pure, EStateM.pure, Bool.not_true, Bool.false_eq_true, active,
        overlayCall]
      refine ⟨_, other, rfl, ?_, overlayRegs.trans queryRegs,
        overlayMem.trans queryMem, overlayEvents.trans queryEvents⟩
      have overlayR := congrArg Prod.fst overlayMeaning
      have overlayW := congrArg (fun rights => rights.2.1) overlayMeaning
      have overlayX := congrArg (fun rights => rights.2.2) overlayMeaning
      change overlay.or = _ at overlayR
      change overlay.ow = _ at overlayW
      change overlay.ox = _ at overlayX
      have overlayTuple : (overlay.or, overlay.ow, overlay.ox) =
          currentOverlayRights ws.permissions state.regs := overlayMeaning
      by_cases wxn : base.wxn = 1#1 <;> by_cases executable : overlay.ox = 1#1 <;>
        simp [computedControlProjection, finishControls, baseControlProjection, overlayProjection,
          active, wxn, executable, ← overlayR, ← overlayX] <;>
        simpa only [executable] using overlayTuple

#print axioms after_base_permissions_total

end ArmCertWalk
