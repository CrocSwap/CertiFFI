import ArmCertTranslateModel.TranslationAgreesCurrent

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- Executable check of `HostRegimeAt` (register fields only). -/
def checkHostRegime (regs : Regs) : Bool :=
  decide (regs.FeatureImpl[7] = true ∧ regs.FeatureImpl[3] = false ∧ regs.FeatureImpl[232] = false ∧
    regs.PSTATE.nRW = 0#1 ∧ _get_TCR_EL2_Type_TG0 (regs.bank_BitVec_64 .TCR_EL2) = 0#2 ∧
    _get_HCR_EL2_Type_E2H (regs.bank_BitVec_64 .HCR_EL2) = 1#1 ∧
    (regs.FeatureImpl[178] = true → _get_TCR2_EL2_Type_D128 (regs.bank_BitVec_64 .TCR2_EL2) = 0#1) ∧
    (regs.FeatureImpl[178] = true → _get_TCR2_EL2_Type_AIE (regs.bank_BitVec_64 .TCR2_EL2) = 0#1) ∧
    (regs.FeatureImpl[178] = true → _get_TCR2_EL2_Type_PnCH (regs.bank_BitVec_64 .TCR2_EL2) = 0#1) ∧
    BitVec.slice (regs.bank_BitVec_64 .TCR_EL2) 59 1 = 0#1)

theorem check_host_regime_sound (state : State) (checked : checkHostRegime state.regs = true) :
    HostRegimeAt state := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := of_decide_eq_true checked
  exact ⟨a, b, c, d, e, f, g, h, i, j⟩

/-- Executable check of `PhysicalAt`. -/
def checkPhysical (config : PhysicalConfig) (regs : Regs) : Bool :=
  decide ((config.paMax = 32 ∨ config.paMax = 36 ∨ config.paMax = 40 ∨ config.paMax = 42 ∨
      config.paMax = 44 ∨ config.paMax = 48 ∨ config.paMax = 52 ∨ config.paMax = 56) ∧
    regs.bank_Int .__supported_pa_size = config.paMax ∧ regs.FeatureImpl[69] = config.lpa ∧
    regs.FeatureImpl[156] = config.lpa2)

theorem check_physical_sound (config : PhysicalConfig) (state : State)
    (checked : checkPhysical config state.regs = true) : PhysicalAt config state := by
  obtain ⟨legal, pa, lpa, lpa2⟩ := of_decide_eq_true checked
  exact ⟨legal, pa, lpa, lpa2⟩

/-- Executable check of `HostWalkAt`. -/
def checkHostWalk (config : AttributeConfig) (controls : S1LogicalReference.Controls)
    (physicalConfig : PhysicalConfig) (regs : Regs) : Bool :=
  checkHostRegime regs && (checkHostPermissionControls regs controls &&
    (checkPhysical physicalConfig regs &&
      decide (physicalConfig.ips = _get_TCR_EL2_Type_IPS (regs.bank_BitVec_64 .TCR_EL2) ∧
        _get_SCTLR_EL2_Type_EE (regs.bank_BitVec_64 .SCTLR_EL2) = 0#1 ∧
        config.mair = regs.bank_BitVec_64 .MAIR_EL2 ∧ regs.FeatureImpl[166] = config.xs ∧
        regs.FeatureImpl[134] = config.mte2 ∧ (regs.PSTATE.EL = 0#2 ∨ regs.PSTATE.EL = 1#2))))

theorem check_host_walk_sound {config : AttributeConfig} {controls : S1LogicalReference.Controls}
    {physicalConfig : PhysicalConfig} (state : State)
    (checked : checkHostWalk config controls physicalConfig state.regs = true) :
    HostWalkAt config controls physicalConfig state := by
  simp only [checkHostWalk, Bool.and_eq_true] at checked
  obtain ⟨regime, controlsChecked, physical, rest⟩ := checked
  obtain ⟨ips, endian, mair, xs, mte2, el⟩ := of_decide_eq_true rest
  exact ⟨check_host_regime_sound state regime,
    check_host_permission_controls_sound _ _ controlsChecked,
    check_physical_sound _ state physical, ips, endian, mair, xs, mte2, el⟩

/-- Executable initial producer for the canonical current invariant. Every
    conjunct is an existing checker or a decidable register equality; the
    `__tlb_enabled` value is the model initializer's (SDK InitTLBFrame). -/
def checkCurrentS1 {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (state : State) : Bool :=
  checkPermissionRowsCovered rows (rowsFootprint spec.imageRows) &&
  (checkImage spec.imageRows (spec.params.pie == 1#1) (spec.params.ha == 1#1)
      (spec.params.hd == 1#1) state.mem &&
  (checkAttributeImage spec.imageRows config &&
  (checkWriteBackAttributeImage spec.imageRows config &&
  (checkPermissionImage rows spec.params state.regs spec.controls state.mem &&
  (checkHostWalk config spec.controls spec.physicalConfig state.regs &&
  (checkHostImageParams state.regs
      {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (state.regs.bank_BitVec_64 .TCR_EL2)} &&
  (checkNormalizedTxsz state.regs spec.params &&
  (checkHostTranslateGuard state.regs spec.params &&
  (decide (sourceTxszFault state.regs
      {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (state.regs.bank_BitVec_64 .TCR_EL2)} = false) &&
  (currentTranslationEnabled state.regs &&
  decide (state.regs.bank_Bool .__tlb_enabled = false)))))))))))

theorem current_s1_of_check {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (state : State)
    (checked : checkCurrentS1 spec config rows state = true) :
    CurrentS1At spec config rows state := by
  simp only [checkCurrentS1, Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨covered, bytes, attributes, writeback, permissions, host, core, geometry, guard, rawFault,
    enabled, cache⟩ := checked
  exact ⟨check_current_images_sound spec config rows state covered bytes attributes writeback permissions,
    check_host_walk_sound state host, check_host_image_params_sound _ _ core,
    check_normalized_txsz_sound _ _ geometry, check_host_translate_guard_sound _ _ guard,
    rawFault, enabled, cache⟩

/-- Executable per-query current access check. -/
def checkCurrentS1Access {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (query : AccessQuery) (data : S1AccessData spec config rows query) (state : State) : Bool :=
  checkCurrentLayout spec.layout spec.params query.va state.regs &&
  (checkTranslateQuery state.regs spec.params query.va query.request.raw &&
  (decide (currentWalkEPD state.regs query.va = 0#1) &&
  (checkLeafMap mapping spec.physicalConfig state.regs query data.leafLevel data.view &&
  checkOutputCache query.request.raw state.regs)))

theorem current_s1_access_of_check {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (query : AccessQuery) (data : S1AccessData spec config rows query) (state : State)
    (checked : checkCurrentS1Access spec config rows mapping query data state = true) :
    CurrentS1AccessAt spec config rows mapping query data state := by
  simp only [checkCurrentS1Access, Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨layout, checks, epd, map, output⟩ := checked
  exact ⟨check_current_layout_sound _ _ _ _ layout, check_translate_query_sound _ _ _ _ checks, epd,
    check_leaf_map_sound _ _ _ _ _ _ map, check_output_cache_sound _ _ output⟩

#print axioms check_host_regime_sound
#print axioms check_physical_sound
#print axioms check_host_walk_sound
#print axioms current_s1_of_check
#print axioms current_s1_access_of_check
end ArmCert.Translate.Model
