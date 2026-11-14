import ArmCertTranslateModel.CurrentBinding
import ArmCertTranslateModel.CurrentImages
import ArmCertWalk.HostDisCHBinding

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- The six scalar links needed to rebind current images, row attribute keys
    and root geometry to the actual getter. These fix structural DATA to the
    current register reads, not register values or inactive parameter words. -/
structure HostImageParamsAt (regs : Regs) (params : S1TTWParams) : Prop where
  ha : params.ha = hostHA regs
  hd : params.hd = hostHD regs
  pie : params.pie = hostPIE regs
  wxn : params.wxn = _get_SCTLR_EL2_Type_WXN (regs.bank_BitVec_64 .SCTLR_EL2)
  mtx : params.mtx = (if regs.FeatureImpl[191] then Sail.BitVec.extractLsb (regs.bank_BitVec_64 .TCR_EL2) 60 60 else 0#1)
  txsz : params.txsz = _get_TCR_EL2_Type_T0SZ (regs.bank_BitVec_64 .TCR_EL2)

def checkHostImageParams (regs : Regs) (params : S1TTWParams) : Bool :=
  decide (params.ha = hostHA regs) && decide (params.hd = hostHD regs) &&
  decide (params.pie = hostPIE regs) &&
  decide (params.wxn = _get_SCTLR_EL2_Type_WXN (regs.bank_BitVec_64 .SCTLR_EL2)) &&
  decide (params.mtx = (if regs.FeatureImpl[191] then Sail.BitVec.extractLsb (regs.bank_BitVec_64 .TCR_EL2) 60 60 else 0#1)) &&
  decide (params.txsz = _get_TCR_EL2_Type_T0SZ (regs.bank_BitVec_64 .TCR_EL2))

theorem check_host_image_params_sound (regs : Regs) (params : S1TTWParams)
    (checked : checkHostImageParams regs params = true) : HostImageParamsAt regs params := by
  simp only [checkHostImageParams, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact ⟨checked.1.1.1.1.1, checked.1.1.1.1.2, checked.1.1.1.2, checked.1.1.2, checked.1.2, checked.2⟩

structure ImageParamsEq (before after : S1TTWParams) : Prop where
  ha : before.ha = after.ha
  hd : before.hd = after.hd
  pie : before.pie = after.pie
  wxn : before.wxn = after.wxn
  mtx : before.mtx = after.mtx
  txsz : before.txsz = after.txsz

theorem HostImageParamsAt.actual {regs : Regs} {before after : S1TTWParams}
    (bound : HostImageParamsAt regs before)
    (shape : HostLower.Shape (regs.bank_BitVec_64 .TCR_EL2) (regs.bank_BitVec_64 .MAIR_EL2) after)
    (flags : HostFlagShape regs after) (reads : HostAdmissionShape regs after) : ImageParamsEq before after := by
  obtain ⟨_, _, _, _, _, _, actualTxsz, _⟩ := shape
  exact ⟨bound.ha.trans flags.1.symm, bound.hd.trans flags.2.1.symm,
    bound.pie.trans flags.2.2.1.symm, bound.wxn.trans reads.2.2.1.symm,
    bound.mtx.trans reads.2.1.symm, bound.txsz.trans actualTxsz.symm⟩

theorem HostImageParamsAt.guarded_page {regs : Regs} {params : S1TTWParams}
    (current : HostImageParamsAt regs params) (guarded : Bool) :
    HostImageParamsAt (gpRegs regs guarded) params :=
  ⟨current.ha, current.hd, current.pie, current.wxn, current.mtx, current.txsz⟩

/-- Rebind all current images on the SAME actual getter successor. DisCH is
    extracted from that very call; there is no second getter invocation and
    no equality of whole parameter records or undefined choice seeds. -/
theorem host_getter_current_images_total {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (state : State)
    (regime : HostRegimeAt state) (bound : HostImageParamsAt state.regs spec.params)
    (controls : HostPermissionControlsAt state.regs spec.controls)
    (images : CurrentImagesAt spec config rows state) :
    ∃ params next,
      AArch64_S1TTWParamsEL20 .SS_NonSecure .VARange_LOWER state = .ok params next ∧
      S1Normality.Frame state next ∧
      HostLower.Shape (state.regs.bank_BitVec_64 .TCR_EL2) (state.regs.bank_BitVec_64 .MAIR_EL2) params ∧
      HostFlagShape state.regs params ∧ HostAdmissionShape state.regs params ∧
      params.disch = 0#1 ∧ ImageParamsEq spec.params params ∧
      CurrentImagesAt {spec with params := params} config rows next ∧
      LeafPermissionControls params (outputOverlayEnabled next.regs) spec.controls ∧
      spec.controls.hpd = (params.hpd == 1#1) := by
  obtain ⟨params, next, call, frame, shape, flags, reads⟩ := host_getter_admission_total state regime
  have active := bound.actual shape flags reads
  have currentImages := (images.reparam params active.ha active.hd active.pie active.wxn).frame frame.1 frame.2.1
  have leaf : LeafPermissionControls params (outputOverlayEnabled next.regs) spec.controls := by
    rw [frame.1]
    exact controls.leaf flags reads
  exact ⟨params, next, call, frame, shape, flags, reads, host_disch_of_call state regime params next call,
    active, currentImages, leaf, controls.hpd_binding reads⟩

#print axioms check_host_image_params_sound
#print axioms HostImageParamsAt.actual
#print axioms HostImageParamsAt.guarded_page
#print axioms host_getter_current_images_total
end ArmCert.Translate.Model
