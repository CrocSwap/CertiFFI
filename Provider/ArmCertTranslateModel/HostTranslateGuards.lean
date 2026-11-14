import ArmCertTranslateModel.NormalizedGetterBinding

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

/-- Exact lower-EL20 getter projections from the pinned source assignments.
    Feature numbers are checked below, not guessed or assigned false. -/
def currentHostGuardView (regs : Regs) : TranslateGuardView :=
  ⟨_get_TCR_EL2_Type_TBI0 (regs.bank_BitVec_64 .TCR_EL2),
    if regs.FeatureImpl[98] then _get_TCR_EL2_Type_TBID0 (regs.bank_BitVec_64 .TCR_EL2) else 0#1,
    if (if regs.FeatureImpl[81] then true else regs.FeatureImpl[227]) then
      _get_TCR_EL2_Type_NFD0 (regs.bank_BitVec_64 .TCR_EL2) else 0#1,
    if regs.FeatureImpl[127] then _get_TCR_EL2_Type_E0PD0 (regs.bank_BitVec_64 .TCR_EL2) else 0#1⟩

def HostTranslateGuardAt (regs : Regs) (params : S1TTWParams) : Prop :=
  translateGuardView params = currentHostGuardView regs

def checkHostTranslateGuard (regs : Regs) (params : S1TTWParams) : Bool :=
  decide (translateGuardView params = currentHostGuardView regs)

theorem check_host_translate_guard_sound (regs : Regs) (params : S1TTWParams)
    (checked : checkHostTranslateGuard regs params = true) : HostTranslateGuardAt regs params := by
  change translateGuardView params = currentHostGuardView regs
  exact of_decide_eq_true checked

def HostTranslateGuardGood (regs : Regs) :
    EStateM.Result (Sail.Error exception) State S1TTWParams → Prop
  | .ok params _ => HostTranslateGuardAt regs params
  | .error _ _ => False

theorem host_native_translate_guards (state : State) :
    HostTranslateGuardGood state.regs (hostNative state) := by
  observe_simp [HostTranslateGuardGood, HostTranslateGuardAt, translateGuardView,
    currentHostGuardView, hostNative, HostLowerSource.native]
  all_goals simp [_get_TCR_EL2_Type_TBID0, _get_TCR_EL2_Type_NFD0, _get_TCR_EL2_Type_E0PD0]

/-- Derive the four fields from THIS actual lower-getter call. This is an
    internal past-call projection, not a public future-success premise. -/
theorem host_translate_guards_of_call (state : State) (regime : HostRegimeAt state)
    (params : S1TTWParams) (next : State)
    (call : AArch64_S1TTWParamsEL20 .SS_NonSecure .VARange_LOWER state = .ok params next) :
    HostTranslateGuardAt state.regs params := by
  have fields := host_native_translate_guards state
  rw [← host_getter_native_eq state regime, call] at fields
  exact fields

theorem host_normalized_translate_guards_of_call (state : State) (regime : HostRegimeAt state)
    (params : S1TTWParams) (next : State)
    (call : AArch64_S1TTWParamsEL20 .SS_NonSecure .VARange_LOWER state = .ok params next) :
    HostTranslateGuardAt state.regs (normalizeWalkParams state.regs params) := by
  change translateGuardView _ = _
  rw [translate_guard_view_normalize]
  exact host_translate_guards_of_call state regime params next call

/-- Source query checks transfer by only four guard fields, MTX and effective
    TxSZ. The actual raw getter and its normalized value share the SAME seed. -/
theorem normalized_translate_query_checks {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (state : State) (regime : HostRegimeAt state) (query : AccessQuery) (raw : S1TTWParams) (next : State)
    (call : AArch64_S1TTWParamsEL20 .SS_NonSecure .VARange_LOWER state = .ok raw next)
    (registers : next.regs = state.regs)
    (active : ImageParamsEq spec.params (normalizeWalkParams state.regs raw))
    (guard : HostTranslateGuardAt state.regs spec.params)
    (checked : TranslateQueryChecks state.regs spec.params query.va query.request.raw) :
    TranslateQueryChecks next.regs (normalizeWalkParams state.regs raw) query.va query.request.raw := by
  have actual := host_normalized_translate_guards_of_call state regime raw next call
  have same : translateGuardView spec.params = translateGuardView (normalizeWalkParams state.regs raw) :=
    guard.trans actual.symm
  rw [registers]
  exact TranslateQueryChecks.reparam state.regs spec.params _ query.va query.request.raw active.txsz active.mtx same checked

/-- Structural current-state inputs produce the actual raw getter call and
    all normalized walk/query inputs on its SAME successor. The raw TxSZ fault
    condition is the source's literal current-state check, not a range pin. -/
theorem host_getter_normalized_query_total {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (query : AccessQuery) (state : State)
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
      AArch64_S1TTWParamsEL20 .SS_NonSecure .VARange_LOWER state = .ok raw next ∧
      S1Normality.Frame state next ∧
      ImageParamsEq spec.params (normalizeWalkParams state.regs raw) ∧
      CurrentImagesAt {spec with params := normalizeWalkParams state.regs raw} config rows next ∧
      WalkFormat (normalizeWalkParams state.regs raw) spec.physicalConfig spec.controls ∧
      WalkCalleesAt (normalizeWalkParams state.regs raw) spec.physicalConfig spec.controls config next ∧
      CurrentLayoutAt spec.layout (normalizeWalkParams state.regs raw) query.va next.regs ∧
      (normalizeWalkParams state.regs raw).disch = 0#1 ∧
      sourceTxszFault next.regs raw = false ∧
      TranslateQueryChecks next.regs (normalizeWalkParams state.regs raw) query.va query.request.raw := by
  obtain ⟨raw, next, call, frame, active, afterImages, format, callees, actualLayout, disch, faultEq⟩ :=
    host_getter_normalized_current_total spec config rows query state current bound geometry layout images
  refine ⟨raw, next, call, frame, active, afterImages, format, callees, actualLayout, disch, ?_, ?_⟩
  · rw [frame.1, faultEq, rawFault]
  · exact normalized_translate_query_checks spec state current.regime query raw next call frame.1 active guard checked

theorem host_guard_feature_indices : num_of_Feature .FEAT_PAuth = 98 ∧
    num_of_Feature .FEAT_SVE = 81 ∧ num_of_Feature .FEAT_TME = 227 ∧
    num_of_Feature .FEAT_E0PD = 127 := by decide

#print axioms check_host_translate_guard_sound
#print axioms host_native_translate_guards
#print axioms host_translate_guards_of_call
#print axioms host_normalized_translate_guards_of_call
#print axioms normalized_translate_query_checks
#print axioms host_getter_normalized_query_total
#print axioms host_guard_feature_indices
end ArmCert.Translate.Model
