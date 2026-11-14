import TranslateSpan.SecpDefaultEntry

open Sail ArmFull ArmFull.Functions ArmCertWalk ArmCert.Translate ArmCert.Translate.Model
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryActualFetch NativeAccess
open NativeMteTagCheck TranslateSpan TranslateSpan.EntryControls TranslateSpan.DefaultMTE2
set_option autoImplicit false
set_option maxHeartbeats 300000

namespace TranslateSpan.SecpEntryComponents

theorem notReset_iff (kind : BranchType) :
    EntryControls.notReset kind = true ↔ kind ≠ .BranchType_RESET := by
  cases kind <;> simp [EntryControls.notReset]

def stepPinsLeaves (s : NativeState) : Prop :=
  ((s.regs.FeatureImpl[4] = true ∧ s.regs.FeatureImpl[232] = false ∧
    s.regs.bank_Bool .SPESampleInFlight = false ∧ s.regs.PSTATE.EL = 0#2 ∧ s.regs.PSTATE.nRW = 0#1 ∧
    _get_EDECR_Type_RCE (s.regs.bank_BitVec_32 .EDECR) = 0#1 ∧
    _get_CTIDEVCTL_Type_RCE (s.regs.bank_BitVec_32 .CTIDEVCTL) = 0#1 ∧
    _get_EDSCR_Type_STATUS (s.regs.bank_BitVec_32 ._EDSCR) = 0b000010#6 ∧
    s.regs.bank_BitVec_32 .EDESR = 0#32 ∧ s.regs.__emulator_termination_opcode = none ∧
    _get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1 ∧
    _get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1 ∧
    _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1 ∧
    _get_PMBLIMITR_EL1_Type_E (s.regs.bank_BitVec_64 .PMBLIMITR_EL1) = 0#1 ∧
    _get_MDSCR_EL1_Type_SS (s.regs.bank_BitVec_64 .MDSCR_EL1) = 0#1 ∧
    Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 .PMBSR_EL1) 17 17 = 0#1 ∧
    s.regs.PSTATE.A = 0#1 ∧ s.regs.PSTATE.I = 0#1 ∧ s.regs.PSTATE.F = 0#1 ∧
    s.regs.PSTATE.IL = 0#1 ∧ s.regs.PSTATE.SS = 0#1 ∧ s.regs.PSTATE.BTYPE = 0#2 ∧
    s.regs.BTypeNext = 0#2) ∧
    (s.regs.Branchtypetaken) ≠ .BranchType_RESET)

theorem stepPins_iff (s : NativeState) :
    TranslateSpan.EntryControls.checkStepPins s = true ↔ stepPinsLeaves s := by
  simp only [TranslateSpan.EntryControls.checkStepPins, stepPinsLeaves, notReset_iff, Bool.and_eq_true, decide_eq_true_eq]

def featuresLeaves (s : NativeState) : Prop :=
  (s.regs.FeatureImpl[0] = false ∧ s.regs.FeatureImpl[1] = false ∧
    s.regs.FeatureImpl[2] = false ∧ s.regs.FeatureImpl[3] = false ∧
    s.regs.FeatureImpl[5] = true ∧ s.regs.FeatureImpl[6] = true ∧
    s.regs.FeatureImpl[7] = true ∧ s.regs.FeatureImpl[54] = true)

theorem features_iff (s : NativeState) :
    TranslateSpan.EntryControls.checkFeatures s = true ↔ featuresLeaves s := by
  simp only [TranslateSpan.EntryControls.checkFeatures, featuresLeaves, decide_eq_true_eq]

def profileLeaves (profile : NativeAccess.AccessProfile) (s : NativeState) : Prop :=
  (s.regs.FeatureImpl[111] = profile.lse2 ∧ s.regs.FeatureImpl[190] = profile.lrcpc3 ∧
    _get_SCTLR_EL2_Type_A (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1)

theorem profile_iff (profile : NativeAccess.AccessProfile) (s : NativeState) :
    TranslateSpan.EntryControls.checkProfile profile s = true ↔ profileLeaves profile s := by
  simp only [TranslateSpan.EntryControls.checkProfile, profileLeaves, decide_eq_true_eq]

def coreExtrasLeaves (s : NativeState) : Prop :=
  (s.regs.FeatureImpl[227] = false ∧ s.regs.FeatureImpl[111] = true ∧ currentDCache s.regs = true)

theorem coreExtras_iff (s : NativeState) :
    TranslateSpan.EntryControls.checkCoreExtras s = true ↔ coreExtrasLeaves s := by
  simp only [TranslateSpan.EntryControls.checkCoreExtras, coreExtrasLeaves, decide_eq_true_eq]

def noUpdateLeaves {domain : QueryDomain} (spec : TopologyImageSpec domain) (s : NativeState) : Prop :=
  ((NoUpdateRows {spec.params with haft := hostHAFT s.regs} (QueryDescriptors.data false) spec.imageRows) = true ∧
    (NoUpdateRows {spec.params with haft := hostHAFT s.regs} (QueryDescriptors.data true) spec.imageRows) = true)

theorem noUpdate_iff {domain : QueryDomain} (spec : TopologyImageSpec domain) (s : NativeState) :
    TranslateSpan.EntryControls.checkNoUpdate spec s = true ↔ noUpdateLeaves spec s := by
  simp only [TranslateSpan.EntryControls.checkNoUpdate, noUpdateLeaves, Bool.and_eq_true]

def debugLeaves (s : NativeState) : Prop :=
  (_get_MDSCR_EL1_Type_MDE (s.regs.bank_BitVec_64 .MDSCR_EL1) = 0#1 ∧
    _get_EDSCR_Type_HDE (s.regs.bank_BitVec_32 ._EDSCR) = 0#1)

theorem debug_iff (s : NativeState) :
    TranslateSpan.EntryControls.checkDebug s = true ↔ debugLeaves s := by
  simp only [TranslateSpan.EntryControls.checkDebug, debugLeaves, decide_eq_true_eq]

def gicLeaves (s : NativeState) : Prop :=
  ((s.regs.bank_Option_InterruptID .__GIC_Pending).isNone) = true

theorem gic_iff (s : NativeState) :
    TranslateSpan.EntryControls.checkGIC s = true ↔ gicLeaves s := by
  simp only [TranslateSpan.EntryControls.checkGIC, gicLeaves]

def quietLeaves (ticks : Nat) (s : NativeState) : Prop :=
  (ArmCert.HookQuiet.V0.feature s.regs .FEAT_AA64EL0 = true ∧
    s.regs.PSTATE.EL = 0#2 ∧ s.regs.PSTATE.nRW = 0#1 ∧
    _get_SCR_EL3_Type_RW (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1 ∧
    _get_HCR_EL2_Type_RW (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1 ∧
    (ArmCert.HookQuiet.V0.feature s.regs .FEAT_RME = false ∨
      _get_SCR_EL3_Type_NSE (s.regs.bank_BitVec_64 .SCR_EL3) = 0#1 ∨
      ArmCert.HookQuiet.V0.effectiveNS s.regs = 1#1) ∧
    s.regs.bank_Bool .SPESampleInFlight = false ∧ s.regs.bank_BitVec_64 .PMINTENCLR_EL1 = 0#64 ∧
    _get_BRBFCR_EL1_Type_PAUSED (s.regs.bank_BitVec_64 .BRBFCR_EL1) = 1#1 ∧
    0 ≤ s.regs.bank_Int .NUM_PMU_COUNTERS ∧ s.regs.bank_Int .NUM_PMU_COUNTERS ≤ 31 ∧
    _get_CNTCR_Type_SCEN (s.regs.bank_BitVec_32 .CNTCR) = 0#1 ∧ ArmCert.HookQuiet.V0.TimersQuiet ticks s.regs)

theorem quiet_iff (ticks : Nat) (s : NativeState) :
    TranslateSpan.EntryControls.checkQuiet ticks s = true ↔ quietLeaves ticks s := by
  simp only [TranslateSpan.EntryControls.checkQuiet, quietLeaves, decide_eq_true_eq]

def branchExtrasLeaves (s : NativeState) : Prop :=
  (s.regs.FeatureImpl[245] = false)

theorem branchExtras_iff (s : NativeState) :
    TranslateSpan.EntryControls.checkBranchExtras s = true ↔ branchExtrasLeaves s := by
  simp only [TranslateSpan.EntryControls.checkBranchExtras, branchExtrasLeaves, decide_eq_true_eq]

def branchLeaves (s : NativeState) : Prop :=
  (((((((s.regs.FeatureImpl[0] = false) ∧
    (s.regs.FeatureImpl[1] = false)) ∧
    ((s.regs.FeatureImpl[2] = false) ∧
    ((s.regs.FeatureImpl[3] = false) ∧
    (s.regs.FeatureImpl[4] = true)))) ∧
    (((s.regs.FeatureImpl[5] = true) ∧
    (s.regs.FeatureImpl[6] = true)) ∧
    ((s.regs.FeatureImpl[7] = true) ∧
    ((s.regs.FeatureImpl[12] = true) ∧
    (s.regs.FeatureImpl[153] = true))))) ∧
    ((((s.regs.FeatureImpl[13] = true) ∧
    (s.regs.FeatureImpl[143] = true)) ∧
    ((s.regs.FeatureImpl[230] = false) ∧
    ((s.regs.FeatureImpl[123] = true) ∧
    (s.regs.FeatureImpl[45] = true)))) ∧
    (((s.regs.FeatureImpl[144] = true) ∧
    ((s.regs.FeatureImpl[103] = true) ∧
    (s.regs.FeatureImpl[60] = true))) ∧
    ((s.regs.FeatureImpl[126] = true) ∧
    ((s.regs.FeatureImpl[185] = false) ∧
    (s.regs.FeatureImpl[105] = true)))))) ∧
    (((((s.regs.FeatureImpl[145] = true) ∧
    (s.regs.FeatureImpl[89] = true)) ∧
    ((s.regs.FeatureImpl[107] = true) ∧
    ((s.regs.FeatureImpl[27] = true) ∧
    (s.regs.FeatureImpl[65] = true)))) ∧
    (((s.regs.FeatureImpl[130] = true) ∧
    (s.regs.FeatureImpl[108] = true)) ∧
    ((s.regs.FeatureImpl[131] = true) ∧
    ((s.regs.FeatureImpl[67] = true) ∧
    (s.regs.FeatureImpl[92] = true))))) ∧
    ((((s.regs.FeatureImpl[93] = true) ∧
    (s.regs.FeatureImpl[110] = true)) ∧
    ((s.regs.FeatureImpl[50] = true) ∧
    ((s.regs.FeatureImpl[111] = true) ∧
    (s.regs.FeatureImpl[171] = false)))) ∧
    (((s.regs.FeatureImpl[133] = true) ∧
    ((s.regs.FeatureImpl[95] = false) ∧
    (s.regs.FeatureImpl[200] = false))) ∧
    ((s.regs.FeatureImpl[36] = true) ∧
    ((s.regs.FeatureImpl[53] = true) ∧
    (s.regs.FeatureImpl[232] = false))))))) ∧
    ((((((s.regs.FeatureImpl[138] = true) ∧
    (s.regs.FeatureImpl[40] = true)) ∧
    ((s.regs.FeatureImpl[41] = true) ∧
    ((s.regs.FeatureImpl[76] = true) ∧
    (s.regs.FeatureImpl[77] = true)))) ∧
    (((s.regs.FeatureImpl[78] = true) ∧
    (s.regs.FeatureImpl[79] = true)) ∧
    ((s.regs.FeatureImpl[233] = false) ∧
    ((s.regs.FeatureImpl[234] = false) ∧
    (s.regs.FeatureImpl[235] = false))))) ∧
    ((((s.regs.FeatureImpl[236] = false) ∧
    (s.regs.FeatureImpl[81] = true)) ∧
    ((s.regs.FeatureImpl[221] = true) ∧
    ((s.regs.FeatureImpl[222] = true) ∧
    (s.regs.FeatureImpl[223] = true)))) ∧
    (((s.regs.FeatureImpl[224] = true) ∧
    ((s.regs.FeatureImpl[225] = true) ∧
    (s.regs.FeatureImpl[226] = true))) ∧
    ((s.regs.FeatureImpl[227] = false) ∧
    ((s.regs.FeatureImpl[165] = true) ∧
    (s.regs.bank_Int .NUM_BREAKPOINTS = 6)))))) ∧
    (((((s.regs.bank_Int .NUM_WATCHPOINTS = 4) ∧
    (s.regs.bank_Int .__num_ctx_breakpoints = 2)) ∧
    ((_get_EDSCR_Type_STATUS (s.regs.bank_BitVec_32 ._EDSCR) = 0b000010#6) ∧
    ((s.regs.bank_Bool .SPESampleInFlight = false) ∧
    (s.regs.PSTATE.EL = 0#2)))) ∧
    (((s.regs.PSTATE.nRW = 0#1) ∧
    (s.regs.PSTATE.IL = 0#1)) ∧
    ((_get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1) ∧
    ((_get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1) ∧
    (_get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1))))) ∧
    ((((_get_SCR_EL3_Type_NSE (s.regs.bank_BitVec_64 .SCR_EL3) = 0#1) ∧
    (_get_MDSCR_EL1_Type_SS (s.regs.bank_BitVec_64 .MDSCR_EL1) = 0#1)) ∧
    ((s.regs.PSTATE.SS = 0#1) ∧
    ((_get_EDESR_Type_OSUC (s.regs.bank_BitVec_32 .EDESR) = 0#1) ∧
    (_get_PMBLIMITR_EL1_Type_E (s.regs.bank_BitVec_64 .PMBLIMITR_EL1) = 0#1)))) ∧
    (((_get_SCR_EL3_Type_RW (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1) ∧
    ((_get_SCR_EL3_Type_EEL2 (s.regs.bank_BitVec_64 .SCR_EL3) = 0#1) ∧
    (_get_TCR_EL2_Type_TBI0 (s.regs.bank_BitVec_64 .TCR_EL2) = 1#1))) ∧
    ((_get_TCR_EL2_Type_TBID0 (s.regs.bank_BitVec_64 .TCR_EL2) = 0#1) ∧
    ((_get_MDCR_EL3_Type_NSPB (s.regs.bank_BitVec_64 .MDCR_EL3) = 0b11#2) ∧
    (_get_MDCR_EL3_Type_NSPBE (s.regs.bank_BitVec_64 .MDCR_EL3) = 0#1))))))))

theorem branch_iff (s : NativeState) :
    TranslateSpan.BranchEntryMTE2.check s = true ↔ branchLeaves s := by
  simp only [TranslateSpan.BranchEntryMTE2.check, branchLeaves, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

def hostPermissionsLeaves (regs : Regs) (controls : S1LogicalReference.Controls) : Prop :=
  ((controls.regime = .el20) ∧
    ((controls.ha = (hostHA regs == 1#1)) ∧
    ((controls.hd = (hostHD regs == 1#1)) ∧
    ((controls.pie = (hostPIE regs == 1#1)) ∧
    ((controls.hpd = ((if regs.FeatureImpl[48] then
    Sail.BitVec.extractLsb (regs.bank_BitVec_64 .TCR_EL2) 41 41 else 0#1) == 1#1)) ∧
    (((controls.pie) = false ∨
    ((controls.pir = Mk_S1PIRType (regs.bank_BitVec_64 .PIR_EL2)) ∧
    (controls.pire0 = Mk_S1PIRType (regs.bank_BitVec_64 .PIRE0_EL2)))) ∧
    ((controls.poe || controls.e0poe) = outputOverlayEnabled regs)))))))

theorem hostPermissions_iff (regs : Regs) (controls : S1LogicalReference.Controls) :
    ArmCert.Translate.Model.checkHostPermissionControls regs controls = true ↔ hostPermissionsLeaves regs controls := by
  cases h : controls.pie <;> simp only [h, Bool.not_false, Bool.not_true, Bool.true_eq_false, Bool.false_eq_true,  false_or, true_or, and_true, true_and, ArmCert.Translate.Model.checkHostPermissionControls, hostPermissionsLeaves, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, and_assoc]

def hostImageLeaves (regs : Regs) (params : S1TTWParams) : Prop :=
  ((params.ha = hostHA regs) ∧
    ((params.hd = hostHD regs) ∧
    ((params.pie = hostPIE regs) ∧
    ((params.wxn = _get_SCTLR_EL2_Type_WXN (regs.bank_BitVec_64 .SCTLR_EL2)) ∧
    ((params.mtx = (if regs.FeatureImpl[191] then Sail.BitVec.extractLsb (regs.bank_BitVec_64 .TCR_EL2) 60 60 else 0#1)) ∧
    (params.txsz = _get_TCR_EL2_Type_T0SZ (regs.bank_BitVec_64 .TCR_EL2)))))))

theorem hostImage_iff (regs : Regs) (params : S1TTWParams) :
    ArmCert.Translate.Model.checkHostImageParams regs params = true ↔ hostImageLeaves regs params := by
  simp only [ArmCert.Translate.Model.checkHostImageParams, hostImageLeaves, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

def normalizedTxszLeaves (regs : Regs) (params : S1TTWParams) : Prop :=
  (params.txsz = normalizeTxsz regs (_get_TCR_EL2_Type_T0SZ (regs.bank_BitVec_64 .TCR_EL2)))

theorem normalizedTxsz_iff (regs : Regs) (params : S1TTWParams) :
    ArmCert.Translate.Model.checkNormalizedTxsz regs params = true ↔ normalizedTxszLeaves regs params := by
  simp only [ArmCert.Translate.Model.checkNormalizedTxsz, normalizedTxszLeaves, decide_eq_true_eq]

def translateGuardLeaves (regs : Regs) (params : S1TTWParams) : Prop :=
  (translateGuardView params = currentHostGuardView regs)

theorem translateGuard_iff (regs : Regs) (params : S1TTWParams) :
    ArmCert.Translate.Model.checkHostTranslateGuard regs params = true ↔ translateGuardLeaves regs params := by
  simp only [ArmCert.Translate.Model.checkHostTranslateGuard, translateGuardLeaves, decide_eq_true_eq]

def hostRegimeLeaves (regs : Regs) : Prop :=
  (regs.FeatureImpl[7] = true ∧ regs.FeatureImpl[3] = false ∧ regs.FeatureImpl[232] = false ∧
    regs.PSTATE.nRW = 0#1 ∧ _get_TCR_EL2_Type_TG0 (regs.bank_BitVec_64 .TCR_EL2) = 0#2 ∧
    _get_HCR_EL2_Type_E2H (regs.bank_BitVec_64 .HCR_EL2) = 1#1 ∧
    (regs.FeatureImpl[178] = true → _get_TCR2_EL2_Type_D128 (regs.bank_BitVec_64 .TCR2_EL2) = 0#1) ∧
    (regs.FeatureImpl[178] = true → _get_TCR2_EL2_Type_AIE (regs.bank_BitVec_64 .TCR2_EL2) = 0#1) ∧
    (regs.FeatureImpl[178] = true → _get_TCR2_EL2_Type_PnCH (regs.bank_BitVec_64 .TCR2_EL2) = 0#1) ∧
    BitVec.slice (regs.bank_BitVec_64 .TCR_EL2) 59 1 = 0#1)

theorem hostRegime_iff (regs : Regs) :
    ArmCert.Translate.Model.checkHostRegime regs = true ↔ hostRegimeLeaves regs := by
  simp only [ArmCert.Translate.Model.checkHostRegime, hostRegimeLeaves, decide_eq_true_eq]

def physicalLeaves (config : PhysicalConfig) (regs : Regs) : Prop :=
  ((config.paMax = 32 ∨ config.paMax = 36 ∨ config.paMax = 40 ∨ config.paMax = 42 ∨
      config.paMax = 44 ∨ config.paMax = 48 ∨ config.paMax = 52 ∨ config.paMax = 56) ∧
    regs.bank_Int .__supported_pa_size = config.paMax ∧ regs.FeatureImpl[69] = config.lpa ∧
    regs.FeatureImpl[156] = config.lpa2)

theorem physical_iff (config : PhysicalConfig) (regs : Regs) :
    ArmCert.Translate.Model.checkPhysical config regs = true ↔ physicalLeaves config regs := by
  simp only [ArmCert.Translate.Model.checkPhysical, physicalLeaves, decide_eq_true_eq]

def hostWalkLeaves (config : AttributeConfig) (controls : S1LogicalReference.Controls)
    (physicalConfig : PhysicalConfig) (regs : Regs) : Prop :=
  (hostRegimeLeaves regs ∧
    (hostPermissionsLeaves regs controls ∧
    (physicalLeaves physicalConfig regs ∧
    (physicalConfig.ips = _get_TCR_EL2_Type_IPS (regs.bank_BitVec_64 .TCR_EL2) ∧
        _get_SCTLR_EL2_Type_EE (regs.bank_BitVec_64 .SCTLR_EL2) = 0#1 ∧
        config.mair = regs.bank_BitVec_64 .MAIR_EL2 ∧ regs.FeatureImpl[166] = config.xs ∧
        regs.FeatureImpl[134] = config.mte2 ∧
    (regs.PSTATE.EL = 0#2 ∨ regs.PSTATE.EL = 1#2)))))

theorem hostWalk_iff (config : AttributeConfig) (controls : S1LogicalReference.Controls)
    (physicalConfig : PhysicalConfig) (regs : Regs) :
    ArmCert.Translate.Model.checkHostWalk config controls physicalConfig regs = true ↔ hostWalkLeaves config controls physicalConfig regs := by
  simp only [ArmCert.Translate.Model.checkHostWalk, hostWalkLeaves, hostPermissions_iff, hostRegime_iff, physical_iff, Bool.and_eq_true, decide_eq_true_eq]

def currentS1Leaves {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (state : ArmCert.Translate.Model.State) : Prop :=
  ((checkPermissionRowsCovered rows (rowsFootprint spec.imageRows)) = true ∧
    ((checkImage spec.imageRows (spec.params.pie == 1#1) (spec.params.ha == 1#1)
      (spec.params.hd == 1#1) state.mem) = true ∧
    ((checkAttributeImage spec.imageRows config) = true ∧
    ((checkWriteBackAttributeImage spec.imageRows config) = true ∧
    ((checkPermissionImage rows spec.params state.regs spec.controls state.mem) = true ∧
    (hostWalkLeaves config spec.controls spec.physicalConfig state.regs ∧
    (hostImageLeaves state.regs
      {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (state.regs.bank_BitVec_64 .TCR_EL2)} ∧
    (normalizedTxszLeaves state.regs spec.params ∧
    (translateGuardLeaves state.regs spec.params ∧
    ((sourceTxszFault state.regs
      {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (state.regs.bank_BitVec_64 .TCR_EL2)} = false) ∧
    ((currentTranslationEnabled state.regs) = true ∧
    (state.regs.bank_Bool .__tlb_enabled = false))))))))))))

theorem currentS1_iff {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (state : ArmCert.Translate.Model.State) :
    ArmCert.Translate.Model.checkCurrentS1 spec config rows state = true ↔ currentS1Leaves spec config rows state := by
  simp only [ArmCert.Translate.Model.checkCurrentS1, currentS1Leaves, hostImage_iff, normalizedTxsz_iff, translateGuard_iff, hostWalk_iff, Bool.and_eq_true, decide_eq_true_eq]

def memoryLeaves (catalogue : ControlCatalogue) (s : NativeState) : Prop :=
  (_get_SCTLR_EL2_Type_E0E (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1 ∧
    s.regs.PSTATE.TCO = 0#1 ∧
    _get_SCTLR_EL2_Type_TCF0 (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#2 ∧
    s.regs.bank_BitVec_64 .TCR_EL2 = catalogue.tcrEL2 ∧
    s.regs.bank_BitVec_64 .SCTLR_EL2 = catalogue.sctlrEL2 ∧
    s.regs.bank_BitVec_64 .HCR_EL2 = catalogue.hcrEL2 ∧
    s.regs.bank_BitVec_64 .SCR_EL3 = catalogue.scrEL3)

theorem memory_iff (catalogue : ControlCatalogue) (s : NativeState) :
    TranslateSpan.DefaultMTE2.checkMemory catalogue s = true ↔ memoryLeaves catalogue s := by
  simp only [TranslateSpan.DefaultMTE2.checkMemory, memoryLeaves, decide_eq_true_eq]

def controlsLeaves {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (profile : AccessProfile)
    (catalogue : ControlCatalogue) (pc : BitVec 64) (budget : Nat) (s : NativeState) : Prop :=
  (stepPinsLeaves s ∧
    (featuresLeaves s ∧
    (debugLeaves s ∧
    (quietLeaves budget s ∧
    (gicLeaves s ∧
    (memoryLeaves catalogue s ∧
    (noUpdateLeaves spec s ∧
    (coreExtrasLeaves s ∧
    (profileLeaves profile s ∧
    ((s.regs._PC = pc) ∧ currentS1Leaves spec config rows (beforeFetchState s)))))))))))

theorem controls_iff {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (profile : AccessProfile)
    (catalogue : ControlCatalogue) (pc : BitVec 64) (budget : Nat) (s : NativeState) :
    TranslateSpan.DefaultMTE2.checkControls spec config rows profile catalogue pc budget s = true ↔ controlsLeaves spec config rows profile catalogue pc budget s := by
  simp only [TranslateSpan.DefaultMTE2.checkControls, controlsLeaves, stepPins_iff, features_iff, profile_iff, coreExtras_iff, noUpdate_iff, debug_iff, gic_iff, quiet_iff, currentS1_iff, memory_iff, Bool.and_eq_true, decide_eq_true_eq]

open SecpRawDeployment

def rawLeaves (p : Plan) (image : MemReloc.Image) (raw : CheckedTopology.Raw)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) : Prop :=
  ∃ topology : CheckedTopology.check raw (addresses p base entry) 4 = true,
    let spec := CheckedTopology.spec raw (addresses p base entry) 4 topology
    controlsLeaves spec config rows (SecpRawDeployment.profile entry) catalogue
      (base + offset p 0) p.code.length entry ∧
    MachineEntry.checkPlaced (codeOffsets p) image base mapping entry = true ∧
    MachineEntry.checkPresent p.regions (view p mapping entry) entry = true ∧
    CheckedEntry.checkQueries spec config rows mapping 1030 (queries p base entry) 4
      (beforeFetchState entry) = true ∧
    checkLayout p raw mapping base entry = true

theorem raw_iff (p : Plan) (image : MemReloc.Image) (raw : CheckedTopology.Raw)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) :
    SecpDefaultEntry.checkRaw p image raw config rows mapping base entry catalogue = true ↔
      rawLeaves p image raw config rows mapping base entry catalogue := by
  unfold SecpDefaultEntry.checkRaw rawLeaves
  split
  · rename_i topology
    simp only [Bool.and_eq_true, controls_iff, and_assoc]
    constructor
    · intro components
      exact ⟨topology, components⟩
    · rintro ⟨_, components⟩
      exact components
  · rename_i topology
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨checked, _⟩
    exact topology checked

def entryLeaves (p : Plan) (image : MemReloc.Image) (raw : CheckedTopology.Raw)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (capacity : Nat) (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) : Prop :=
  rawLeaves p image raw config rows mapping base entry catalogue ∧
  branchLeaves entry ∧ branchExtrasLeaves entry ∧
  (base.toNat % 4096 = 0 ∧ (entryGPR entry 30).toNat < 2 ^ 55) ∧
  (∀ site ∈ sites p entry, SelectedLoadFacts.checkTargets mapping site.address = true) ∧
  TagStatusRows.check capacity entry = true

theorem entry_iff (p : Plan) (image : MemReloc.Image) (raw : CheckedTopology.Raw)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (capacity : Nat) (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) :
    SecpDefaultEntry.check p image raw config rows mapping base capacity entry catalogue = true ↔
      entryLeaves p image raw config rows mapping base capacity entry catalogue := by
  simp only [SecpDefaultEntry.check, entryLeaves, Bool.and_eq_true, decide_eq_true_eq,
    raw_iff, branch_iff, branchExtras_iff, List.all_eq_true, and_assoc]

#print axioms raw_iff
#print axioms entry_iff

#print axioms stepPins_iff
#print axioms features_iff
#print axioms profile_iff
#print axioms coreExtras_iff
#print axioms noUpdate_iff
#print axioms debug_iff
#print axioms gic_iff
#print axioms quiet_iff
#print axioms branchExtras_iff
#print axioms branch_iff
#print axioms hostPermissions_iff
#print axioms hostImage_iff
#print axioms normalizedTxsz_iff
#print axioms translateGuard_iff
#print axioms hostRegime_iff
#print axioms physical_iff
#print axioms hostWalk_iff
#print axioms currentS1_iff
#print axioms memory_iff
#print axioms controls_iff

end TranslateSpan.SecpEntryComponents
