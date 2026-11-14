-- Transparent scalar getter checks for the one machine entry.
import NativeAccess.Control
import ArmCertPipe.ChainInvG
import TranslateSpan.QueryDescriptors
open Sail ArmFull ArmFull.Functions ArmCertWalk ArmCert.Translate.Model ArmBridge.Draft
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded.EntryActualFetch
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.EntryControls

def notReset (kind : BranchType) : Bool :=
  match kind with
  | .BranchType_RESET => false
  | _ => true

theorem notReset_sound (kind : BranchType) (checked : notReset kind = true) :
    kind ≠ .BranchType_RESET := by
  intro equal
  subst kind
  simp [notReset] at checked

def checkStepPins (s : NativeState) : Bool :=
  decide (s.regs.FeatureImpl[4] = true ∧ s.regs.FeatureImpl[232] = false ∧
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
    s.regs.BTypeNext = 0#2) && notReset s.regs.Branchtypetaken

theorem stepPins_of_check (s : NativeState) (checked : checkStepPins s = true) : StepPins s := by
  simp only [checkStepPins,Bool.and_eq_true] at checked
  obtain ⟨f4,rme,spe,el,nrw,edecr,cti,status,edesr,emu,e2h,tge,ns,pmbe,mdss,pmbs,da,di,df,il,pss,btype,btn⟩ :=
    of_decide_eq_true checked.1
  exact ⟨by simpa using f4,by simpa using rme,spe,el,nrw,edecr,cti,status,edesr,
    notReset_sound _ checked.2,emu,e2h,tge,ns,pmbe,mdss,pmbs,da,di,df,il,pss,btype,btn⟩

def checkFeatures (s : NativeState) : Bool :=
  decide (s.regs.FeatureImpl[0] = false ∧ s.regs.FeatureImpl[1] = false ∧
    s.regs.FeatureImpl[2] = false ∧ s.regs.FeatureImpl[3] = false ∧
    s.regs.FeatureImpl[5] = true ∧ s.regs.FeatureImpl[6] = true ∧
    s.regs.FeatureImpl[7] = true ∧ s.regs.FeatureImpl[54] = true)

theorem features_of_check (s : NativeState) (checked : checkFeatures s = true) : EntryFeatures s.regs := by
  obtain ⟨a0,a1,a2,a3,b1,b2,b3,vhe⟩ := of_decide_eq_true checked
  exact ⟨a0,a1,a2,a3,b1,b2,b3,vhe⟩

def checkProfile (profile : NativeAccess.AccessProfile) (s : NativeState) : Bool :=
  decide (s.regs.FeatureImpl[111] = profile.lse2 ∧ s.regs.FeatureImpl[190] = profile.lrcpc3 ∧
    _get_SCTLR_EL2_Type_A (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1)

theorem profile_of_check (profile : NativeAccess.AccessProfile) (s : NativeState)
    (pins : StepPins s) (features : EntryFeatures s.regs) (checked : checkProfile profile s = true) :
    NativeAccess.ProfileAt profile s := by
  obtain ⟨lse2,lrcpc3,alignment⟩ := of_decide_eq_true checked
  exact ⟨lse2,lrcpc3,⟨pins.el,pins.nrw,pins.f4,pins.rme,by simpa using features.vhe,
    pins.scrns,pins.e2h,pins.tge⟩,alignment⟩

def checkCoreExtras (s : NativeState) : Bool :=
  decide (s.regs.FeatureImpl[227] = false ∧ s.regs.FeatureImpl[111] = true ∧ currentDCache s.regs = true)

theorem extras_of_check (s : NativeState) (features : EntryFeatures s.regs)
    (checked : checkCoreExtras s = true) :
    (s.regs.FeatureImpl[7] = true ∧ s.regs.FeatureImpl[3] = false ∧
      s.regs.FeatureImpl[227] = false ∧ s.regs.FeatureImpl[111] = true) ∧ currentDCache s.regs = true := by
  obtain ⟨tme,lse2,cache⟩ := of_decide_eq_true checked
  exact ⟨⟨features.b3,features.a3,tme,lse2⟩,cache⟩

theorem noUpdate_data_eq (params : S1TTWParams) (rows : List ImageRow) (write : Bool)
    (a b : AccessDescriptor) (ha : DataShape write a) (hb : DataShape write b) :
    NoUpdateRows params a rows = NoUpdateRows params b rows := by
  unfold NoUpdateRows RowNoUpdate leafUpdateWord leafDirtyEnabled
  rw [ha.write,hb.write,ha.acctype,hb.acctype]

def checkNoUpdate {domain : QueryDomain} (spec : TopologyImageSpec domain) (s : NativeState) : Bool :=
  NoUpdateRows {spec.params with haft := hostHAFT s.regs} (QueryDescriptors.data false) spec.imageRows &&
  NoUpdateRows {spec.params with haft := hostHAFT s.regs} (QueryDescriptors.data true) spec.imageRows

theorem noUpdate_of_check {domain : QueryDomain} (spec : TopologyImageSpec domain) (s : NativeState)
    (checked : checkNoUpdate spec s = true) :
    ∀ write acc, DataShape write acc →
      NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true := by
  simp only [checkNoUpdate,Bool.and_eq_true] at checked
  intro write acc shape
  rw [noUpdate_data_eq _ _ write acc (QueryDescriptors.data write) shape (QueryDescriptors.data_shape write)]
  cases write with
  | false => exact checked.1
  | true => exact checked.2

theorem mode_of_checks (s : NativeState) (pins : StepPins s) (features : EntryFeatures s.regs) :
    HostEL0ModeAt s.regs :=
  ⟨features.a2,features.b2,features.vhe,pins.el,pins.scrns,pins.tge⟩

def checkDebug (s : NativeState) : Bool :=
  decide (_get_MDSCR_EL1_Type_MDE (s.regs.bank_BitVec_64 .MDSCR_EL1) = 0#1 ∧
    _get_EDSCR_Type_HDE (s.regs.bank_BitVec_32 ._EDSCR) = 0#1)

theorem debug_of_check (s : NativeState) (checked : checkDebug s = true) :
    ExistingE11DebugAt s.regs ∧ ArmBridge.CruxGenGuarded.E11Debug.E11CheckDebug s.regs := by
  obtain ⟨mde,hde⟩ := of_decide_eq_true checked
  exact ⟨⟨mde,hde⟩,⟨mde,hde⟩⟩

def checkMemoryControls (s : NativeState) : Bool :=
  decide (_get_SCTLR_EL2_Type_E0E (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1 ∧
    s.regs.FeatureImpl[134] = false)

theorem post2_of_check (s : NativeState) (pins : StepPins s) (features : EntryFeatures s.regs)
    (checked : checkMemoryControls s = true) : MemM1.MemReadD2.PostRegs2 s.regs := by
  obtain ⟨endian,noMTE2⟩ := of_decide_eq_true checked
  exact ⟨⟨pins.spe,pins.el,pins.nrw,by simpa using pins.rme,features.vhe,
    by simpa using pins.f4,pins.scrns,pins.e2h,pins.tge,endian⟩,noMTE2⟩

def checkGIC (s : NativeState) : Bool :=
  (s.regs.bank_Option_InterruptID .__GIC_Pending).isNone

theorem gic_of_check (s : NativeState) (checked : checkGIC s = true) :
    s.regs.bank_Option_InterruptID .__GIC_Pending = none := by
  cases h : s.regs.bank_Option_InterruptID .__GIC_Pending with
  | none => rfl
  | some irq => simp [checkGIC,h] at checked

@[instance_reducible] private def deadlineDec (ticks : Nat) (r : Regs) (offset compare : BitVec 64) :
    Decidable (ArmCert.HookQuiet.V0.Deadline ticks r offset compare) := by
  unfold ArmCert.HookQuiet.V0.Deadline
  infer_instance
attribute [local instance] deadlineDec
@[instance_reducible] private def timerDec (ticks : Nat) (r : Regs) (active : Bool)
    (ctl compare offset : BitVec 64) (mask : Bool) :
    Decidable (ArmCert.HookQuiet.V0.TimerQuiet ticks r active ctl compare offset mask) := by
  unfold ArmCert.HookQuiet.V0.TimerQuiet
  infer_instance
attribute [local instance] timerDec
@[instance_reducible] private def timersDec (ticks : Nat) (r : Regs) : Decidable (ArmCert.HookQuiet.V0.TimersQuiet ticks r) := by
  unfold ArmCert.HookQuiet.V0.TimersQuiet
  infer_instance
attribute [local instance] timersDec

/-- Existing quiet predicate expanded into current getter fields and timer
arithmetic. No future hook execution or success is an input. -/
def checkQuiet (ticks : Nat) (s : NativeState) : Bool :=
  decide (ArmCert.HookQuiet.V0.feature s.regs .FEAT_AA64EL0 = true ∧
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

theorem quiet_of_check (ticks : Nat) (s : NativeState) (checked : checkQuiet ticks s = true) :
    ArmCert.HookQuiet.V0.HookQuiet ticks s := by
  obtain ⟨a64,el0,nrw,scrRW,hcrRW,security,spe,pmu,brbe,lower,upper,ordinary,timers⟩ := of_decide_eq_true checked
  exact ⟨a64,el0,nrw,scrRW,hcrRW,security,spe,pmu,brbe,lower,upper,ordinary,timers⟩

#print axioms mode_of_checks
#print axioms checkDebug
#print axioms debug_of_check
#print axioms checkMemoryControls
#print axioms post2_of_check
#print axioms checkGIC
#print axioms gic_of_check
#print axioms checkQuiet
#print axioms quiet_of_check
-- BEGIN GENERATED: exact SDKPA.BranchPins scalar fields.
def checkBranchBase (s : NativeState) : Bool :=
  ((((((decide (s.regs.FeatureImpl[0] = false) &&
    decide (s.regs.FeatureImpl[1] = false)) &&
    (decide (s.regs.FeatureImpl[2] = false) &&
    (decide (s.regs.FeatureImpl[3] = false) &&
    decide (s.regs.FeatureImpl[4] = true)))) &&
    ((decide (s.regs.FeatureImpl[5] = true) &&
    decide (s.regs.FeatureImpl[6] = true)) &&
    (decide (s.regs.FeatureImpl[7] = true) &&
    (decide (s.regs.FeatureImpl[12] = true) &&
    decide (s.regs.FeatureImpl[153] = true))))) &&
    (((decide (s.regs.FeatureImpl[13] = true) &&
    decide (s.regs.FeatureImpl[143] = true)) &&
    (decide (s.regs.FeatureImpl[230] = false) &&
    (decide (s.regs.FeatureImpl[123] = true) &&
    decide (s.regs.FeatureImpl[45] = true)))) &&
    ((decide (s.regs.FeatureImpl[144] = true) &&
    (decide (s.regs.FeatureImpl[103] = true) &&
    decide (s.regs.FeatureImpl[60] = true))) &&
    (decide (s.regs.FeatureImpl[126] = true) &&
    (decide (s.regs.FeatureImpl[185] = false) &&
    decide (s.regs.FeatureImpl[105] = true)))))) &&
    ((((decide (s.regs.FeatureImpl[145] = true) &&
    decide (s.regs.FeatureImpl[89] = true)) &&
    (decide (s.regs.FeatureImpl[107] = true) &&
    (decide (s.regs.FeatureImpl[27] = true) &&
    decide (s.regs.FeatureImpl[65] = true)))) &&
    ((decide (s.regs.FeatureImpl[130] = true) &&
    decide (s.regs.FeatureImpl[108] = true)) &&
    (decide (s.regs.FeatureImpl[131] = true) &&
    (decide (s.regs.FeatureImpl[67] = true) &&
    decide (s.regs.FeatureImpl[92] = true))))) &&
    (((decide (s.regs.FeatureImpl[93] = true) &&
    decide (s.regs.FeatureImpl[110] = true)) &&
    (decide (s.regs.FeatureImpl[50] = true) &&
    (decide (s.regs.FeatureImpl[111] = true) &&
    decide (s.regs.FeatureImpl[171] = false)))) &&
    ((decide (s.regs.FeatureImpl[133] = true) &&
    (decide (s.regs.FeatureImpl[134] = false) &&
    decide (s.regs.FeatureImpl[95] = false))) &&
    (decide (s.regs.FeatureImpl[200] = false) &&
    (decide (s.regs.FeatureImpl[36] = true) &&
    decide (s.regs.FeatureImpl[53] = true))))))) &&
    (((((decide (s.regs.FeatureImpl[232] = false) &&
    decide (s.regs.FeatureImpl[138] = true)) &&
    (decide (s.regs.FeatureImpl[40] = true) &&
    (decide (s.regs.FeatureImpl[41] = true) &&
    decide (s.regs.FeatureImpl[76] = true)))) &&
    ((decide (s.regs.FeatureImpl[77] = true) &&
    decide (s.regs.FeatureImpl[78] = true)) &&
    (decide (s.regs.FeatureImpl[79] = true) &&
    (decide (s.regs.FeatureImpl[233] = false) &&
    decide (s.regs.FeatureImpl[234] = false))))) &&
    (((decide (s.regs.FeatureImpl[235] = false) &&
    decide (s.regs.FeatureImpl[236] = false)) &&
    (decide (s.regs.FeatureImpl[81] = true) &&
    (decide (s.regs.FeatureImpl[221] = true) &&
    decide (s.regs.FeatureImpl[222] = true)))) &&
    ((decide (s.regs.FeatureImpl[223] = true) &&
    (decide (s.regs.FeatureImpl[224] = true) &&
    decide (s.regs.FeatureImpl[225] = true))) &&
    (decide (s.regs.FeatureImpl[226] = true) &&
    (decide (s.regs.FeatureImpl[227] = false) &&
    decide (s.regs.FeatureImpl[165] = true)))))) &&
    ((((decide (s.regs.bank_Int .NUM_BREAKPOINTS = 6) &&
    decide (s.regs.bank_Int .NUM_WATCHPOINTS = 4)) &&
    (decide (s.regs.bank_Int .__num_ctx_breakpoints = 2) &&
    (decide (_get_EDSCR_Type_STATUS (s.regs.bank_BitVec_32 ._EDSCR) = 0b000010#6) &&
    decide (s.regs.bank_Bool .SPESampleInFlight = false)))) &&
    ((decide (s.regs.PSTATE.EL = 0#2) &&
    (decide (s.regs.PSTATE.nRW = 0#1) &&
    decide (s.regs.PSTATE.IL = 0#1))) &&
    (decide (_get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1) &&
    (decide (_get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1) &&
    decide (_get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1))))) &&
    (((decide (_get_SCR_EL3_Type_NSE (s.regs.bank_BitVec_64 .SCR_EL3) = 0#1) &&
    decide (_get_MDSCR_EL1_Type_SS (s.regs.bank_BitVec_64 .MDSCR_EL1) = 0#1)) &&
    (decide (s.regs.PSTATE.SS = 0#1) &&
    (decide (_get_EDESR_Type_OSUC (s.regs.bank_BitVec_32 .EDESR) = 0#1) &&
    decide (_get_PMBLIMITR_EL1_Type_E (s.regs.bank_BitVec_64 .PMBLIMITR_EL1) = 0#1)))) &&
    ((decide (_get_SCR_EL3_Type_RW (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1) &&
    (decide (_get_SCR_EL3_Type_EEL2 (s.regs.bank_BitVec_64 .SCR_EL3) = 0#1) &&
    decide (_get_TCR_EL2_Type_TBI0 (s.regs.bank_BitVec_64 .TCR_EL2) = 1#1))) &&
    (decide (_get_TCR_EL2_Type_TBID0 (s.regs.bank_BitVec_64 .TCR_EL2) = 0#1) &&
    (decide (_get_MDCR_EL3_Type_NSPB (s.regs.bank_BitVec_64 .MDCR_EL3) = 0b11#2) &&
    decide (_get_MDCR_EL3_Type_NSPBE (s.regs.bank_BitVec_64 .MDCR_EL3) = 0#1))))))))

theorem branchBase_of_check (s : NativeState) (checked : checkBranchBase s = true) : Crypto.BranchPinsPA s := by
  simp only [checkBranchBase, Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨⟨⟨⟨⟨⟨p0,p1⟩,⟨p2,⟨p3,p4⟩⟩⟩,⟨⟨p5,p6⟩,⟨p7,⟨p8,p9⟩⟩⟩⟩,⟨⟨⟨p10,p11⟩,⟨p12,⟨p13,p14⟩⟩⟩,⟨⟨p15,⟨p16,p17⟩⟩,⟨p18,⟨p19,p20⟩⟩⟩⟩⟩,⟨⟨⟨⟨p21,p22⟩,⟨p23,⟨p24,p25⟩⟩⟩,⟨⟨p26,p27⟩,⟨p28,⟨p29,p30⟩⟩⟩⟩,⟨⟨⟨p31,p32⟩,⟨p33,⟨p34,p35⟩⟩⟩,⟨⟨p36,⟨p37,p38⟩⟩,⟨p39,⟨p40,p41⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨p42,p43⟩,⟨p44,⟨p45,p46⟩⟩⟩,⟨⟨p47,p48⟩,⟨p49,⟨p50,p51⟩⟩⟩⟩,⟨⟨⟨p52,p53⟩,⟨p54,⟨p55,p56⟩⟩⟩,⟨⟨p57,⟨p58,p59⟩⟩,⟨p60,⟨p61,p62⟩⟩⟩⟩⟩,⟨⟨⟨⟨p63,p64⟩,⟨p65,⟨p66,p67⟩⟩⟩,⟨⟨p68,⟨p69,p70⟩⟩,⟨p71,⟨p72,p73⟩⟩⟩⟩,⟨⟨⟨p74,p75⟩,⟨p76,⟨p77,p78⟩⟩⟩,⟨⟨p79,⟨p80,p81⟩⟩,⟨p82,⟨p83,p84⟩⟩⟩⟩⟩⟩⟩ := checked
  exact {
    hFeature_AA32EL0 := by simpa using p0
    hFeature_AA32EL1 := by simpa using p1
    hFeature_AA32EL2 := by simpa using p2
    hFeature_AA32EL3 := by simpa using p3
    hFeature_AA64EL0 := by simpa using p4
    hFeature_AA64EL1 := by simpa using p5
    hFeature_AA64EL2 := by simpa using p6
    hFeature_AA64EL3 := by simpa using p7
    hFeature_AES := by simpa using p8
    hFeature_AFP := by simpa using p9
    hFeature_AdvSIMD := by simpa using p10
    hFeature_BF16 := by simpa using p11
    hFeature_BRBE := by simpa using p12
    hFeature_BTI := by simpa using p13
    hFeature_CRC32 := by simpa using p14
    hFeature_DGH := by simpa using p15
    hFeature_DIT := by simpa using p16
    hFeature_DPB := by simpa using p17
    hFeature_DPB2 := by simpa using p18
    hFeature_Debugv8p9 := by simpa using p19
    hFeature_DotProd := by simpa using p20
    hFeature_ECV := by simpa using p21
    hFeature_FCMA := by simpa using p22
    hFeature_FHM := by simpa using p23
    hFeature_FP := by simpa using p24
    hFeature_FP16 := by simpa using p25
    hFeature_FRINTTS := by simpa using p26
    hFeature_FlagM := by simpa using p27
    hFeature_FlagM2 := by simpa using p28
    hFeature_I8MM := by simpa using p29
    hFeature_JSCVT := by simpa using p30
    hFeature_LRCPC := by simpa using p31
    hFeature_LRCPC2 := by simpa using p32
    hFeature_LSE := by simpa using p33
    hFeature_LSE2 := by simpa using p34
    hFeature_MOPS := by simpa using p35
    hFeature_MTE := by simpa using p36
    hFeature_MTE2 := by simpa using p37
    hFeature_PACIMP := by simpa using p38
    hFeature_PFAR := by simpa using p39
    hFeature_PMULL := by simpa using p40
    hFeature_RDM := by simpa using p41
    hFeature_RME := by simpa using p42
    hFeature_SB := by simpa using p43
    hFeature_SHA1 := by simpa using p44
    hFeature_SHA256 := by simpa using p45
    hFeature_SHA3 := by simpa using p46
    hFeature_SHA512 := by simpa using p47
    hFeature_SM3 := by simpa using p48
    hFeature_SM4 := by simpa using p49
    hFeature_SME := by simpa using p50
    hFeature_SME_F64F64 := by simpa using p51
    hFeature_SME_FA64 := by simpa using p52
    hFeature_SME_I16I64 := by simpa using p53
    hFeature_SVE := by simpa using p54
    hFeature_SVE2 := by simpa using p55
    hFeature_SVE_AES := by simpa using p56
    hFeature_SVE_BitPerm := by simpa using p57
    hFeature_SVE_PMULL128 := by simpa using p58
    hFeature_SVE_SHA3 := by simpa using p59
    hFeature_SVE_SM4 := by simpa using p60
    hFeature_TME := by simpa using p61
    hFeature_WFxT := by simpa using p62
    hDebugBP := by simpa using p63
    hDebugWP := by simpa using p64
    hDebugCTX := by simpa using p65
    hEDSCR_STATUS := by simpa using p66
    hSPE := by simpa using p67
    hEL := by simpa using p68
    hnRW := by simpa using p69
    hIL := by simpa using p70
    hE2H := by simpa using p71
    hTGE := by simpa using p72
    hSCR_NS := by simpa using p73
    hSCR_NSE := by simpa using p74
    hMDSCR_SS := by simpa using p75
    hPSTATE_SS := by simpa using p76
    hOSUC := by simpa using p77
    hPMB_E := by simpa using p78
    hSCR_RW := by simpa using p79
    hSCR_EEL2 := by simpa using p80
    hTBI0 := by simpa using p81
    hTBID0 := by simpa using p82
    hNSPB := by simpa using p83
    hNSPBE := by simpa using p84
  }

def checkBranchExtras (s : NativeState) : Bool := decide (s.regs.FeatureImpl[245] = false)

theorem branch_of_check (s : NativeState) (features : EntryFeatures s.regs)
    (base : checkBranchBase s = true) (extras : checkBranchExtras s = true) :
    Crypto.BranchV2.BranchPinsV2PA s :=
  ⟨branchBase_of_check s base,features.vhe,of_decide_eq_true extras⟩
#print axioms checkBranchBase
#print axioms branchBase_of_check
#print axioms checkBranchExtras
#print axioms branch_of_check
-- END GENERATED: exact SDKPA.BranchPins scalar fields.

#print axioms notReset
#print axioms notReset_sound
#print axioms checkStepPins
#print axioms stepPins_of_check
#print axioms checkFeatures
#print axioms features_of_check
#print axioms checkProfile
#print axioms profile_of_check
#print axioms checkCoreExtras
#print axioms extras_of_check
#print axioms noUpdate_data_eq
#print axioms checkNoUpdate
#print axioms noUpdate_of_check
end TranslateSpan.EntryControls
