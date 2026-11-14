import ArmCertWalk.TranslateGetterWrapper
import ArmCertTranslateModel.HostTranslateGuards

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk

theorem host_walk_frame (config : AttributeConfig) (controls : S1LogicalReference.Controls)
    (physical : PhysicalConfig) (before after : State)
    (current : HostWalkAt config controls physical before) (registers : after.regs = before.regs) :
    HostWalkAt config controls physical after := by
  refine ⟨current.regime.of_regs registers, ?_, current.physical.of_regs registers, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [registers] using current.controls
  · simpa only [registers] using current.ips
  · simpa only [registers] using current.endian
  · simpa only [registers] using current.mair
  · simpa only [registers] using current.xs
  · simpa only [registers] using current.mte2
  · simpa only [registers] using current.el

/-- The real outer getter wrapper executes its ignored seed before its single
actual lower getter. Normalized geometry and all source guards are derived on
that same successor, retaining the real occurrence state throughout. -/
theorem translate_normalized_entry_total {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (query : AccessQuery) (state : State)
    (lower : AArch64_GetVARange query.va = .VARange_LOWER)
    (current : HostWalkAt config spec.controls spec.physicalConfig state)
    (bound : HostImageParamsAt state.regs
      {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (state.regs.bank_BitVec_64 .TCR_EL2)})
    (geometry : spec.params.txsz = normalizeTxsz state.regs
      (_get_TCR_EL2_Type_T0SZ (state.regs.bank_BitVec_64 .TCR_EL2)))
    (layout : CurrentLayoutAt spec.layout spec.params query.va state.regs)
    (images : CurrentImagesAt spec config rows state)
    (guard : HostTranslateGuardAt state.regs spec.params)
    (checked : TranslateQueryChecks state.regs spec.params query.va query.request.raw)
    (rawFault : sourceTxszFault state.regs
      {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (state.regs.bank_BitVec_64 .TCR_EL2)} = false) :
    ∃ raw next,
      AArch64_GetS1TTWParams .Regime_EL20 .SS_NonSecure query.va state = .ok raw next ∧
      S1Normality.Frame state next ∧
      ImageParamsEq spec.params (normalizeWalkParams state.regs raw) ∧
      CurrentImagesAt {spec with params := normalizeWalkParams state.regs raw} config rows next ∧
      WalkFormat (normalizeWalkParams state.regs raw) spec.physicalConfig spec.controls ∧
      WalkCalleesAt (normalizeWalkParams state.regs raw) spec.physicalConfig spec.controls config next ∧
      CurrentLayoutAt spec.layout (normalizeWalkParams state.regs raw) query.va next.regs ∧
      (normalizeWalkParams state.regs raw).disch = 0#1 ∧
      sourceTxszFault next.regs raw = false ∧
      TranslateQueryChecks next.regs (normalizeWalkParams state.regs raw) query.va query.request.raw := by
  obtain ⟨unused, afterSeed, seedCall, seedFrame⟩ := params_draw_normal 1274 state
  have seedCurrent := host_walk_frame config spec.controls spec.physicalConfig state afterSeed current seedFrame.1
  have seedBound : HostImageParamsAt afterSeed.regs
      {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (afterSeed.regs.bank_BitVec_64 .TCR_EL2)} := by
    simpa only [seedFrame.1] using bound
  obtain ⟨raw, next, call, frame, active, afterImages, format, callees, actualLayout, disch, noFault, checks⟩ :=
    host_getter_normalized_query_total spec config rows query afterSeed seedCurrent seedBound
      (by simpa only [seedFrame.1] using geometry) (layout.of_regs seedFrame.1)
      (images.frame seedFrame.1 seedFrame.2.1) (by simpa only [seedFrame.1] using guard)
      (by simpa only [seedFrame.1] using checked) (by simpa only [seedFrame.1] using rawFault)
  have wrapper : AArch64_GetS1TTWParams .Regime_EL20 .SS_NonSecure query.va state = .ok raw next := by
    rw [get_params_el20_eq, ← bind_assoc]
    change (match (do undefined_S1TTWParams (← occLabel 1274) ()) state with
      | .ok _ next => AArch64_S1TTWParamsEL20 .SS_NonSecure (AArch64_GetVARange query.va) next
      | .error err next => .error err next) = .ok raw next
    rw [seedCall, lower]
    exact call
  rw [seedFrame.1] at active afterImages format callees actualLayout disch checks
  exact ⟨raw, next, wrapper, S1EntryWP.frame_trans seedFrame frame,
    active, afterImages, format, callees, actualLayout, disch, noFault, checks⟩

#print axioms host_walk_frame
#print axioms translate_normalized_entry_total
end ArmCertWalk
