import ArmCertTranslateModel.GetterImageCore
import ArmCertTranslateModel.HostWalkInputs
import ArmCertWalk.TranslateEntryGuards

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

theorem normalize_walk_params_record (regs : Regs) (params : S1TTWParams) :
    normalizeWalkParams regs params = {params with txsz := normalizeTxsz regs params.txsz} := by
  by_cases low : (params.txsz.toNat : Int) < 16 <;>
    by_cases high : (params.txsz.toNat : Int) > currentMaxTxsz regs <;>
    simp only [normalizeWalkParams, normalizeTxsz, low, high, ↓reduceIte]

theorem normalize_walk_params_register_fields (before after : Regs) (params : S1TTWParams)
    (ttst : after.FeatureImpl[122] = before.FeatureImpl[122]) :
    normalizeWalkParams after params = normalizeWalkParams before params := by
  unfold normalizeWalkParams currentMaxTxsz
  rw [ttst]

def checkNormalizedTxsz (regs : Regs) (params : S1TTWParams) : Bool :=
  decide (params.txsz = normalizeTxsz regs (_get_TCR_EL2_Type_T0SZ (regs.bank_BitVec_64 .TCR_EL2)))

theorem check_normalized_txsz_sound (regs : Regs) (params : S1TTWParams)
    (checked : checkNormalizedTxsz regs params = true) :
    params.txsz = normalizeTxsz regs (_get_TCR_EL2_Type_T0SZ (regs.bank_BitVec_64 .TCR_EL2)) :=
  of_decide_eq_true checked

theorem normalize_walk_format (regs : Regs) {params : S1TTWParams} {physical : PhysicalConfig}
    {controls : S1LogicalReference.Controls} (current : WalkFormat params physical controls) :
    WalkFormat (normalizeWalkParams regs params) physical controls := by
  rw [normalize_walk_params_record]
  exact ⟨current.d128, current.ds, current.tg, current.aie, current.pnch, current.endian, current.ips, current.hpd⟩

theorem normalize_walk_callees (regs : Regs) {params : S1TTWParams} {physical : PhysicalConfig}
    {controls : S1LogicalReference.Controls} {config : AttributeConfig} {state : State}
    (current : WalkCalleesAt params physical controls config state) :
    WalkCalleesAt (normalizeWalkParams regs params) physical controls config state := by
  rw [normalize_walk_params_record]
  refine ⟨current.physical, ⟨current.attributes.mair, current.attributes.xs, current.attributes.mte2⟩,
    ?_, current.el, current.noRME, current.aarch64, current.el3A64, current.noEL3A32⟩
  exact ⟨current.permissions.regime, current.permissions.pie, current.permissions.ha, current.permissions.hd,
    current.permissions.pir, current.permissions.pire0, current.permissions.overlayEnabled⟩

/-- Current images and effective geometry bind to the source-normalized value.
    The call equation retains the ACTUAL RAW getter result. Its inactive fields
    remain those of that actual invocation, including all choice bookkeeping.
    Raw TxSZ is unrestricted; its source fault check remains separate. -/
theorem host_getter_normalized_current_total {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (query : AccessQuery) (state : State)
    (current : HostWalkAt config spec.controls spec.physicalConfig state)
    (bound : HostImageParamsAt state.regs
      {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (state.regs.bank_BitVec_64 .TCR_EL2)})
    (geometry : spec.params.txsz = normalizeTxsz state.regs
      (_get_TCR_EL2_Type_T0SZ (state.regs.bank_BitVec_64 .TCR_EL2)))
    (layout : CurrentLayoutAt spec.layout spec.params query.va state.regs)
    (images : CurrentImagesAt spec config rows state) :
    ∃ raw next,
      AArch64_S1TTWParamsEL20 .SS_NonSecure .VARange_LOWER state = .ok raw next ∧
      S1Normality.Frame state next ∧
      ImageParamsEq spec.params (normalizeWalkParams state.regs raw) ∧
      CurrentImagesAt {spec with params := normalizeWalkParams state.regs raw} config rows next ∧
      WalkFormat (normalizeWalkParams state.regs raw) spec.physicalConfig spec.controls ∧
      WalkCalleesAt (normalizeWalkParams state.regs raw) spec.physicalConfig spec.controls config next ∧
      CurrentLayoutAt spec.layout (normalizeWalkParams state.regs raw) query.va next.regs ∧
      (normalizeWalkParams state.regs raw).disch = 0#1 ∧
      sourceTxszFault state.regs raw = sourceTxszFault state.regs
        {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (state.regs.bank_BitVec_64 .TCR_EL2)} := by
  obtain ⟨raw, next, call, frame, shape, flags, reads, disch, active, rawImages, leaf, hpd⟩ :=
    host_getter_image_core_total spec config rows state current.regime bound current.controls images
  have rawTxsz : raw.txsz = _get_TCR_EL2_Type_T0SZ (state.regs.bank_BitVec_64 .TCR_EL2) := active.txsz.symm
  have effective : spec.params.txsz = normalizeTxsz state.regs raw.txsz := by rw [rawTxsz]; exact geometry
  have normalized : ImageParamsEq spec.params (normalizeWalkParams state.regs raw) := by
    rw [normalize_walk_params_record]
    exact image_params_eq_normalized_txsz _ _ _ _ active effective
  obtain ⟨format, callees⟩ := current.getter_inputs raw shape flags reads
  have normalizedImages := (images.reparam _ normalized.ha normalized.hd normalized.pie normalized.wxn).frame frame.1 frame.2.1
  have actualLayout := (current_layout_reparam spec.layout spec.params _ query.va state.regs layout normalized.txsz).of_regs frame.1
  refine ⟨raw, next, call, frame, normalized, normalizedImages, normalize_walk_format state.regs format,
    (normalize_walk_callees state.regs callees).of_regs frame.1, actualLayout, ?_, ?_⟩
  · rw [normalize_walk_params_record]
    exact disch
  · simp only [sourceTxszFault, rawTxsz]

#print axioms normalize_walk_params_record
#print axioms normalize_walk_params_register_fields
#print axioms check_normalized_txsz_sound
#print axioms normalize_walk_format
#print axioms normalize_walk_callees
#print axioms host_getter_normalized_current_total
end ArmCert.Translate.Model
