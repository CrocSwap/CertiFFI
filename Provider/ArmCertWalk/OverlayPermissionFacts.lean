import ArmCertWalk.OverlayPermissionStages
import ArmCertWalk.PermissionWindows

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

namespace ArmCertWalk

def overlayProjection (controls : S1AccessControls) : OverlayRights :=
  (controls.or, controls.ow, controls.ox)

def currentOverlayRights (permissions : Permissions) (registers : Regs) : OverlayRights :=
  overlayRights (permissionNibble (registers.bank_BitVec_64 .POR_EL0) permissions.po_index)

theorem por20_query_eq (state : State) :
    AArch64_S1POR .Regime_EL20 state = .ok (state.regs.bank_BitVec_64 .POR_EL2) state := rfl

theorem por0_query_eq (state : State) :
    (readReg POR_EL0 : SailM (BitVec 64)) state =
      .ok (state.regs.bank_BitVec_64 .POR_EL0) state := rfl

theorem overlay_permission_body_total (ws : TTWState) (input : AccessDescriptor)
    (seed : OverlayPermissionStages.StageAcc) (state : State) :
    ∃ controls, OverlayPermissionStages.body ws input seed state = .ok controls state ∧
      overlayProjection controls = currentOverlayRights ws.permissions state.regs := by
  have has : HasUnprivileged .Regime_EL20 = true := by decide
  simp only [OverlayPermissionStages.body, has, ↓reduceIte,
    DirectPermissionSource.el0Nonsecure, EL0, Bind.bind, EStateM.bind,
    por20_query_eq, por0_query_eq, Pure.pure, EStateM.pure, BEq.rfl]
  refine ⟨_, rfl, ?_⟩
  change overlayRights (sourcePermissionNibble (state.regs.bank_BitVec_64 .POR_EL0)
    ws.permissions.po_index) = _
  rw [sourcePermissionNibble_eq]
  rfl

#print axioms por20_query_eq
#print axioms por0_query_eq
#print axioms overlay_permission_body_total

end ArmCertWalk
