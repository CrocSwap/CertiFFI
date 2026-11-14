import ReleaseProfile.GB10.Source

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024

namespace ReleaseProfile.GB10

open ReleaseProfile.MachineSource

/-- Nonconfiguration register data: the 12 conservative data coordinates plus the page-table roots
TTBR0_EL2/TTBR1_EL2 (boss c2d2 + H1; Doug D265). -/
structure DataPart where
  gpr : Vector (BitVec 64) 31
  SP_EL3 : (BitVec 64)
  SP_EL2 : (BitVec 64)
  SP_EL1 : (BitVec 64)
  SP_EL0 : (BitVec 64)
  _ZT0 : (BitVec 512)
  _ZA : (Vector (BitVec 2048) 256)
  _FFR : (BitVec 256)
  _P : (Vector (BitVec 256) 16)
  _Z : (Vector (BitVec 2048) 32)
  PhysicalCount : (BitVec 88)
  _PC : (BitVec 64)
  TTBR0_EL2 : BitVec 128
  TTBR1_EL2 : BitVec 128
  HTTBR : BitVec 64
  /-- Generic-timer registers (entry data, boss 820e); read at the `isTimerData64` keys. -/
  timers : ArmFull.Bank_BitVec_64 → BitVec 64

def dataOf (regs : ArmFull.Regs) : DataPart where
  gpr := regs.gpr
  SP_EL3 := regs.SP_EL3
  SP_EL2 := regs.SP_EL2
  SP_EL1 := regs.SP_EL1
  SP_EL0 := regs.SP_EL0
  _ZT0 := regs._ZT0
  _ZA := regs._ZA
  _FFR := regs._FFR
  _P := regs._P
  _Z := regs._Z
  PhysicalCount := regs.PhysicalCount
  _PC := regs._PC
  TTBR0_EL2 := regs.bank_BitVec_128 ._TTBR0_EL2
  TTBR1_EL2 := regs.bank_BitVec_128 .TTBR1_EL2
  HTTBR := regs.bank_BitVec_64 .HTTBR
  timers := regs.bank_BitVec_64

/-- The 64-bit bank of the source register file: entry-data keys (HTTBR, generic timers) from data, canonical otherwise. -/
def sourceBank64 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (data : DataPart)
    (key : ArmFull.Bank_BitVec_64) : BitVec 64 :=
  if h : isEntryData64 key = true then (if key = .HTTBR then data.HTTBR else data.timers key)
  else interpret rho.val caller.caller ⟨.bank_BitVec_64 key, bank64_notData key (Bool.eq_false_iff.mpr h)⟩

theorem sourceBank64_ne (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (data : DataPart)
    (key : ArmFull.Bank_BitVec_64) (h : isEntryData64 key = false) :
    sourceBank64 rho caller data key = interpret rho.val caller.caller ⟨.bank_BitVec_64 key, bank64_notData key h⟩ :=
  dif_neg (by simp [h])

theorem sourceBank64_entry (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (data : DataPart)
    (key : ArmFull.Bank_BitVec_64) (h : isEntryData64 key = true) :
    sourceBank64 rho caller data key = (if key = .HTTBR then data.HTTBR else data.timers key) :=
  dif_pos h

/-- The 128-bit bank of the source register file: data for the page-table roots, canonical otherwise. -/
def sourceBank128 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (data : DataPart) :
    ArmFull.Bank_BitVec_128 → BitVec 128
  | ._PAR_EL1 => interpret rho.val caller.caller ⟨.bank_BitVec_128 ._PAR_EL1, rfl⟩
  | .RCWSMASK_EL1 => interpret rho.val caller.caller ⟨.bank_BitVec_128 .RCWSMASK_EL1, rfl⟩
  | .RCWMASK_EL1 => interpret rho.val caller.caller ⟨.bank_BitVec_128 .RCWMASK_EL1, rfl⟩
  | ._VTTBR_EL2 => interpret rho.val caller.caller ⟨.bank_BitVec_128 ._VTTBR_EL2, rfl⟩
  | .TTBR1_EL2 => data.TTBR1_EL2
  | ._TTBR1_EL1 => interpret rho.val caller.caller ⟨.bank_BitVec_128 ._TTBR1_EL1, rfl⟩
  | ._TTBR0_EL2 => data.TTBR0_EL2
  | ._TTBR0_EL1 => interpret rho.val caller.caller ⟨.bank_BitVec_128 ._TTBR0_EL1, rfl⟩

/-- Canonical feature value at an admissible completion (caller independent). -/
def sourceFeature (rho : AdmissibleSourceCompletion) (_caller : AdmissibleCaller rho)
    (index : Fin 259) : Bool :=
  FeatureSource.value rho.val.features index

#check "CURRENT_DECL GB10.sourceRegs"
/-- Source-owned complete register file. Every non-data field is the canonical interpretation
at an admissible completion and caller; only DataPart supplies nonconfiguration data. -/
def sourceRegs (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (data : DataPart) : ArmFull.Regs where
  gpr := data.gpr
  __emulator_termination_opcode := interpret rho.val caller.caller ⟨.__emulator_termination_opcode, rfl⟩
  PMEVCNTSVR_EL1 := interpret rho.val caller.caller ⟨.PMEVCNTSVR_EL1, rfl⟩
  SPESampleCounter := interpret rho.val caller.caller ⟨.SPESampleCounter, rfl⟩
  SPERecordData := interpret rho.val caller.caller ⟨.SPERecordData, rfl⟩
  SP_EL3 := data.SP_EL3
  SP_EL2 := data.SP_EL2
  SP_EL1 := data.SP_EL1
  SP_EL0 := data.SP_EL0
  __mpam_vpmr_max := interpret rho.val caller.caller ⟨.__mpam_vpmr_max, rfl⟩
  __BranchTaken := interpret rho.val caller.caller ⟨.__BranchTaken, rfl⟩
  Branchtypetaken := interpret rho.val caller.caller ⟨.Branchtypetaken, rfl⟩
  __ThisInstrEnc := interpret rho.val caller.caller ⟨.__ThisInstrEnc, rfl⟩
  __SPE_LFSR := interpret rho.val caller.caller ⟨.__SPE_LFSR, rfl⟩
  SPESampleOpType := interpret rho.val caller.caller ⟨.SPESampleOpType, rfl⟩
  TSTATE := interpret rho.val caller.caller ⟨.TSTATE, rfl⟩
  FPSR := interpret rho.val caller.caller ⟨.FPSR, rfl⟩
  FPCR := interpret rho.val caller.caller ⟨.FPCR, rfl⟩
  _ZT0 := data._ZT0
  _ZA := data._ZA
  _FFR := data._FFR
  _P := data._P
  _Z := data._Z
  BTypeCompatible := interpret rho.val caller.caller ⟨.BTypeCompatible, rfl⟩
  BTypeNext := interpret rho.val caller.caller ⟨.BTypeNext, rfl⟩
  RC := interpret rho.val caller.caller ⟨.RC, rfl⟩
  PhysicalCount := data.PhysicalCount
  _PC := data._PC
  ShouldAdvanceSS := interpret rho.val caller.caller ⟨.ShouldAdvanceSS, rfl⟩
  ShouldAdvanceIT := interpret rho.val caller.caller ⟨.ShouldAdvanceIT, rfl⟩
  PSTATE := {
    N := interpret rho.val caller.caller ⟨.pstate_N, rfl⟩
    Z := interpret rho.val caller.caller ⟨.pstate_Z, rfl⟩
    C := interpret rho.val caller.caller ⟨.pstate_C, rfl⟩
    V := interpret rho.val caller.caller ⟨.pstate_V, rfl⟩
    D := interpret rho.val caller.caller ⟨.pstate_D, rfl⟩
    A := interpret rho.val caller.caller ⟨.pstate_A, rfl⟩
    I := interpret rho.val caller.caller ⟨.pstate_I, rfl⟩
    F := interpret rho.val caller.caller ⟨.pstate_F, rfl⟩
    EXLOCK := interpret rho.val caller.caller ⟨.pstate_EXLOCK, rfl⟩
    PAN := interpret rho.val caller.caller ⟨.pstate_PAN, rfl⟩
    UAO := interpret rho.val caller.caller ⟨.pstate_UAO, rfl⟩
    DIT := interpret rho.val caller.caller ⟨.pstate_DIT, rfl⟩
    TCO := interpret rho.val caller.caller ⟨.pstate_TCO, rfl⟩
    PM := interpret rho.val caller.caller ⟨.pstate_PM, rfl⟩
    PPEND := interpret rho.val caller.caller ⟨.pstate_PPEND, rfl⟩
    BTYPE := interpret rho.val caller.caller ⟨.pstate_BTYPE, rfl⟩
    ZA := interpret rho.val caller.caller ⟨.pstate_ZA, rfl⟩
    SM := interpret rho.val caller.caller ⟨.pstate_SM, rfl⟩
    ALLINT := interpret rho.val caller.caller ⟨.pstate_ALLINT, rfl⟩
    SS := interpret rho.val caller.caller ⟨.pstate_SS, rfl⟩
    IL := interpret rho.val caller.caller ⟨.pstate_IL, rfl⟩
    EL := interpret rho.val caller.caller ⟨.pstate_EL, rfl⟩
    nRW := interpret rho.val caller.caller ⟨.pstate_nRW, rfl⟩
    SP := interpret rho.val caller.caller ⟨.pstate_SP, rfl⟩
    Q := interpret rho.val caller.caller ⟨.pstate_Q, rfl⟩
    GE := interpret rho.val caller.caller ⟨.pstate_GE, rfl⟩
    SSBS := interpret rho.val caller.caller ⟨.pstate_SSBS, rfl⟩
    IT := interpret rho.val caller.caller ⟨.pstate_IT, rfl⟩
    J := interpret rho.val caller.caller ⟨.pstate_J, rfl⟩
    T := interpret rho.val caller.caller ⟨.pstate_T, rfl⟩
    E := interpret rho.val caller.caller ⟨.pstate_E, rfl⟩
    M := interpret rho.val caller.caller ⟨.pstate_M, rfl⟩
  }
  PMULastThresholdValue := interpret rho.val caller.caller ⟨.PMULastThresholdValue, rfl⟩
  PMUEventAccumulator := interpret rho.val caller.caller ⟨.PMUEventAccumulator, rfl⟩
  VariantImplemented := interpret rho.val caller.caller ⟨.VariantImplemented, rfl⟩
  FeatureImpl := Vector.ofFn (sourceFeature rho caller)
  bank_BitVec_32 := fun key => interpret rho.val caller.caller ⟨.bank_BitVec_32 key, rfl⟩
  bank_Vector_BitVec_32_16 := fun key => interpret rho.val caller.caller ⟨.bank_Vector_BitVec_32_16 key, rfl⟩
  bank_Vector_BitVec_32_4 := fun key => interpret rho.val caller.caller ⟨.bank_Vector_BitVec_32_4 key, rfl⟩
  bank_Vector_BitVec_64_32 := fun key => interpret rho.val caller.caller ⟨.bank_Vector_BitVec_64_32 key, rfl⟩
  bank_BitVec_64 := sourceBank64 rho caller data
  bank_Vector_BitVec_64_16 := fun key => interpret rho.val caller.caller ⟨.bank_Vector_BitVec_64_16 key, rfl⟩
  bank_Vector_BitVec_64_4 := fun key => interpret rho.val caller.caller ⟨.bank_Vector_BitVec_64_4 key, rfl⟩
  bank_Vector_BitVec_32_31 := fun key => interpret rho.val caller.caller ⟨.bank_Vector_BitVec_32_31 key, rfl⟩
  bank_Bool := fun key => interpret rho.val caller.caller ⟨.bank_Bool key, rfl⟩
  bank_Int := fun key => interpret rho.val caller.caller ⟨.bank_Int key, rfl⟩
  bank_BitVec_1 := fun key => interpret rho.val caller.caller ⟨.bank_BitVec_1 key, rfl⟩
  bank_BitVec_56 := fun key => interpret rho.val caller.caller ⟨.bank_BitVec_56 key, rfl⟩
  bank_BitVec_16 := fun key => interpret rho.val caller.caller ⟨.bank_BitVec_16 key, rfl⟩
  bank_BitVec_4 := fun key => interpret rho.val caller.caller ⟨.bank_BitVec_4 key, rfl⟩
  bank_BitVec_128 := sourceBank128 rho caller data
  bank_Vector_Bool_32 := fun key => interpret rho.val caller.caller ⟨.bank_Vector_Bool_32 key, rfl⟩
  bank_Vector_BitVec_64_64 := fun key => interpret rho.val caller.caller ⟨.bank_Vector_BitVec_64_64 key, rfl⟩
  bank_Option_InterruptID := fun key => interpret rho.val caller.caller ⟨.bank_Option_InterruptID key, rfl⟩
  bank_BitVec_8 := fun key => interpret rho.val caller.caller ⟨.bank_BitVec_8 key, rfl⟩
  bank_BitVec_2 := fun key => interpret rho.val caller.caller ⟨.bank_BitVec_2 key, rfl⟩
  bank_Vector_BitVec_64_7 := fun key => interpret rho.val caller.caller ⟨.bank_Vector_BitVec_64_7 key, rfl⟩
  bank_Signal := fun key => interpret rho.val caller.caller ⟨.bank_Signal key, rfl⟩

#check "CURRENT_DECL GB10.regs_eq_source"
/-- An agreeing actual entry IS the source register file with its own data part. -/
theorem regs_eq_source {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho}
    (configuration : Configuration rho caller) (regs : ArmFull.Regs)
    (agreement : AgreesAt configuration regs) :
    regs = sourceRegs rho caller (dataOf regs) := by
  have actual := actual_coordinate configuration regs agreement
  clear agreement
  obtain ⟨r_gpr, r___emulator_termination_opcode, r_PMEVCNTSVR_EL1, r_SPESampleCounter, r_SPERecordData, r_SP_EL3, r_SP_EL2, r_SP_EL1, r_SP_EL0, r___mpam_vpmr_max, r___BranchTaken, r_Branchtypetaken, r___ThisInstrEnc, r___SPE_LFSR, r_SPESampleOpType, r_TSTATE, r_FPSR, r_FPCR, r__ZT0, r__ZA, r__FFR, r__P, r__Z, r_BTypeCompatible, r_BTypeNext, r_RC, r_PhysicalCount, r__PC, r_ShouldAdvanceSS, r_ShouldAdvanceIT, r_PSTATE, r_PMULastThresholdValue, r_PMUEventAccumulator, r_VariantImplemented, r_FeatureImpl, r_bank_BitVec_32, r_bank_Vector_BitVec_32_16, r_bank_Vector_BitVec_32_4, r_bank_Vector_BitVec_64_32, r_bank_BitVec_64, r_bank_Vector_BitVec_64_16, r_bank_Vector_BitVec_64_4, r_bank_Vector_BitVec_32_31, r_bank_Bool, r_bank_Int, r_bank_BitVec_1, r_bank_BitVec_56, r_bank_BitVec_16, r_bank_BitVec_4, r_bank_BitVec_128, r_bank_Vector_Bool_32, r_bank_Vector_BitVec_64_64, r_bank_Option_InterruptID, r_bank_BitVec_8, r_bank_BitVec_2, r_bank_Vector_BitVec_64_7, r_bank_Signal⟩ := regs
  obtain ⟨p_N, p_Z, p_C, p_V, p_D, p_A, p_I, p_F, p_EXLOCK, p_PAN, p_UAO, p_DIT, p_TCO, p_PM, p_PPEND, p_BTYPE, p_ZA, p_SM, p_ALLINT, p_SS, p_IL, p_EL, p_nRW, p_SP, p_Q, p_GE, p_SSBS, p_IT, p_J, p_T, p_E, p_M⟩ := r_PSTATE
  have h___emulator_termination_opcode : r___emulator_termination_opcode = interpret rho.val caller.caller ⟨.__emulator_termination_opcode, rfl⟩ := actual ⟨.__emulator_termination_opcode, rfl⟩
  have h_PMEVCNTSVR_EL1 : r_PMEVCNTSVR_EL1 = interpret rho.val caller.caller ⟨.PMEVCNTSVR_EL1, rfl⟩ := actual ⟨.PMEVCNTSVR_EL1, rfl⟩
  have h_SPESampleCounter : r_SPESampleCounter = interpret rho.val caller.caller ⟨.SPESampleCounter, rfl⟩ := actual ⟨.SPESampleCounter, rfl⟩
  have h_SPERecordData : r_SPERecordData = interpret rho.val caller.caller ⟨.SPERecordData, rfl⟩ := actual ⟨.SPERecordData, rfl⟩
  have h___mpam_vpmr_max : r___mpam_vpmr_max = interpret rho.val caller.caller ⟨.__mpam_vpmr_max, rfl⟩ := actual ⟨.__mpam_vpmr_max, rfl⟩
  have h___BranchTaken : r___BranchTaken = interpret rho.val caller.caller ⟨.__BranchTaken, rfl⟩ := actual ⟨.__BranchTaken, rfl⟩
  have h_Branchtypetaken : r_Branchtypetaken = interpret rho.val caller.caller ⟨.Branchtypetaken, rfl⟩ := actual ⟨.Branchtypetaken, rfl⟩
  have h___ThisInstrEnc : r___ThisInstrEnc = interpret rho.val caller.caller ⟨.__ThisInstrEnc, rfl⟩ := actual ⟨.__ThisInstrEnc, rfl⟩
  have h___SPE_LFSR : r___SPE_LFSR = interpret rho.val caller.caller ⟨.__SPE_LFSR, rfl⟩ := actual ⟨.__SPE_LFSR, rfl⟩
  have h_SPESampleOpType : r_SPESampleOpType = interpret rho.val caller.caller ⟨.SPESampleOpType, rfl⟩ := actual ⟨.SPESampleOpType, rfl⟩
  have h_TSTATE : r_TSTATE = interpret rho.val caller.caller ⟨.TSTATE, rfl⟩ := actual ⟨.TSTATE, rfl⟩
  have h_FPSR : r_FPSR = interpret rho.val caller.caller ⟨.FPSR, rfl⟩ := actual ⟨.FPSR, rfl⟩
  have h_FPCR : r_FPCR = interpret rho.val caller.caller ⟨.FPCR, rfl⟩ := actual ⟨.FPCR, rfl⟩
  have h_BTypeCompatible : r_BTypeCompatible = interpret rho.val caller.caller ⟨.BTypeCompatible, rfl⟩ := actual ⟨.BTypeCompatible, rfl⟩
  have h_BTypeNext : r_BTypeNext = interpret rho.val caller.caller ⟨.BTypeNext, rfl⟩ := actual ⟨.BTypeNext, rfl⟩
  have h_RC : r_RC = interpret rho.val caller.caller ⟨.RC, rfl⟩ := actual ⟨.RC, rfl⟩
  have h_ShouldAdvanceSS : r_ShouldAdvanceSS = interpret rho.val caller.caller ⟨.ShouldAdvanceSS, rfl⟩ := actual ⟨.ShouldAdvanceSS, rfl⟩
  have h_ShouldAdvanceIT : r_ShouldAdvanceIT = interpret rho.val caller.caller ⟨.ShouldAdvanceIT, rfl⟩ := actual ⟨.ShouldAdvanceIT, rfl⟩
  have h_PMULastThresholdValue : r_PMULastThresholdValue = interpret rho.val caller.caller ⟨.PMULastThresholdValue, rfl⟩ := actual ⟨.PMULastThresholdValue, rfl⟩
  have h_PMUEventAccumulator : r_PMUEventAccumulator = interpret rho.val caller.caller ⟨.PMUEventAccumulator, rfl⟩ := actual ⟨.PMUEventAccumulator, rfl⟩
  have h_VariantImplemented : r_VariantImplemented = interpret rho.val caller.caller ⟨.VariantImplemented, rfl⟩ := actual ⟨.VariantImplemented, rfl⟩
  have h_FeatureImpl : r_FeatureImpl = Vector.ofFn (sourceFeature rho caller) := by
    apply Vector.ext
    intro index bound
    rw [Vector.getElem_ofFn]
    exact actual ⟨.feature ⟨index, bound⟩, rfl⟩
  have h_bank_BitVec_32 : r_bank_BitVec_32 = fun key => interpret rho.val caller.caller ⟨.bank_BitVec_32 key, rfl⟩ :=
    funext fun key => actual ⟨.bank_BitVec_32 key, rfl⟩
  have h_bank_Vector_BitVec_32_16 : r_bank_Vector_BitVec_32_16 = fun key => interpret rho.val caller.caller ⟨.bank_Vector_BitVec_32_16 key, rfl⟩ :=
    funext fun key => actual ⟨.bank_Vector_BitVec_32_16 key, rfl⟩
  have h_bank_Vector_BitVec_32_4 : r_bank_Vector_BitVec_32_4 = fun key => interpret rho.val caller.caller ⟨.bank_Vector_BitVec_32_4 key, rfl⟩ :=
    funext fun key => actual ⟨.bank_Vector_BitVec_32_4 key, rfl⟩
  have h_bank_Vector_BitVec_64_32 : r_bank_Vector_BitVec_64_32 = fun key => interpret rho.val caller.caller ⟨.bank_Vector_BitVec_64_32 key, rfl⟩ :=
    funext fun key => actual ⟨.bank_Vector_BitVec_64_32 key, rfl⟩
  have h_bank_Vector_BitVec_64_16 : r_bank_Vector_BitVec_64_16 = fun key => interpret rho.val caller.caller ⟨.bank_Vector_BitVec_64_16 key, rfl⟩ :=
    funext fun key => actual ⟨.bank_Vector_BitVec_64_16 key, rfl⟩
  have h_bank_Vector_BitVec_64_4 : r_bank_Vector_BitVec_64_4 = fun key => interpret rho.val caller.caller ⟨.bank_Vector_BitVec_64_4 key, rfl⟩ :=
    funext fun key => actual ⟨.bank_Vector_BitVec_64_4 key, rfl⟩
  have h_bank_Vector_BitVec_32_31 : r_bank_Vector_BitVec_32_31 = fun key => interpret rho.val caller.caller ⟨.bank_Vector_BitVec_32_31 key, rfl⟩ :=
    funext fun key => actual ⟨.bank_Vector_BitVec_32_31 key, rfl⟩
  have h_bank_Bool : r_bank_Bool = fun key => interpret rho.val caller.caller ⟨.bank_Bool key, rfl⟩ :=
    funext fun key => actual ⟨.bank_Bool key, rfl⟩
  have h_bank_Int : r_bank_Int = fun key => interpret rho.val caller.caller ⟨.bank_Int key, rfl⟩ :=
    funext fun key => actual ⟨.bank_Int key, rfl⟩
  have h_bank_BitVec_1 : r_bank_BitVec_1 = fun key => interpret rho.val caller.caller ⟨.bank_BitVec_1 key, rfl⟩ :=
    funext fun key => actual ⟨.bank_BitVec_1 key, rfl⟩
  have h_bank_BitVec_56 : r_bank_BitVec_56 = fun key => interpret rho.val caller.caller ⟨.bank_BitVec_56 key, rfl⟩ :=
    funext fun key => actual ⟨.bank_BitVec_56 key, rfl⟩
  have h_bank_BitVec_16 : r_bank_BitVec_16 = fun key => interpret rho.val caller.caller ⟨.bank_BitVec_16 key, rfl⟩ :=
    funext fun key => actual ⟨.bank_BitVec_16 key, rfl⟩
  have h_bank_BitVec_4 : r_bank_BitVec_4 = fun key => interpret rho.val caller.caller ⟨.bank_BitVec_4 key, rfl⟩ :=
    funext fun key => actual ⟨.bank_BitVec_4 key, rfl⟩
  have h_bank_Vector_Bool_32 : r_bank_Vector_Bool_32 = fun key => interpret rho.val caller.caller ⟨.bank_Vector_Bool_32 key, rfl⟩ :=
    funext fun key => actual ⟨.bank_Vector_Bool_32 key, rfl⟩
  have h_bank_Vector_BitVec_64_64 : r_bank_Vector_BitVec_64_64 = fun key => interpret rho.val caller.caller ⟨.bank_Vector_BitVec_64_64 key, rfl⟩ :=
    funext fun key => actual ⟨.bank_Vector_BitVec_64_64 key, rfl⟩
  have h_bank_Option_InterruptID : r_bank_Option_InterruptID = fun key => interpret rho.val caller.caller ⟨.bank_Option_InterruptID key, rfl⟩ :=
    funext fun key => actual ⟨.bank_Option_InterruptID key, rfl⟩
  have h_bank_BitVec_8 : r_bank_BitVec_8 = fun key => interpret rho.val caller.caller ⟨.bank_BitVec_8 key, rfl⟩ :=
    funext fun key => actual ⟨.bank_BitVec_8 key, rfl⟩
  have h_bank_BitVec_2 : r_bank_BitVec_2 = fun key => interpret rho.val caller.caller ⟨.bank_BitVec_2 key, rfl⟩ :=
    funext fun key => actual ⟨.bank_BitVec_2 key, rfl⟩
  have h_bank_Vector_BitVec_64_7 : r_bank_Vector_BitVec_64_7 = fun key => interpret rho.val caller.caller ⟨.bank_Vector_BitVec_64_7 key, rfl⟩ :=
    funext fun key => actual ⟨.bank_Vector_BitVec_64_7 key, rfl⟩
  have h_bank_Signal : r_bank_Signal = fun key => interpret rho.val caller.caller ⟨.bank_Signal key, rfl⟩ :=
    funext fun key => actual ⟨.bank_Signal key, rfl⟩
  have h_pstate_N : p_N = interpret rho.val caller.caller ⟨.pstate_N, rfl⟩ := actual ⟨.pstate_N, rfl⟩
  have h_pstate_Z : p_Z = interpret rho.val caller.caller ⟨.pstate_Z, rfl⟩ := actual ⟨.pstate_Z, rfl⟩
  have h_pstate_C : p_C = interpret rho.val caller.caller ⟨.pstate_C, rfl⟩ := actual ⟨.pstate_C, rfl⟩
  have h_pstate_V : p_V = interpret rho.val caller.caller ⟨.pstate_V, rfl⟩ := actual ⟨.pstate_V, rfl⟩
  have h_pstate_D : p_D = interpret rho.val caller.caller ⟨.pstate_D, rfl⟩ := actual ⟨.pstate_D, rfl⟩
  have h_pstate_A : p_A = interpret rho.val caller.caller ⟨.pstate_A, rfl⟩ := actual ⟨.pstate_A, rfl⟩
  have h_pstate_I : p_I = interpret rho.val caller.caller ⟨.pstate_I, rfl⟩ := actual ⟨.pstate_I, rfl⟩
  have h_pstate_F : p_F = interpret rho.val caller.caller ⟨.pstate_F, rfl⟩ := actual ⟨.pstate_F, rfl⟩
  have h_pstate_EXLOCK : p_EXLOCK = interpret rho.val caller.caller ⟨.pstate_EXLOCK, rfl⟩ := actual ⟨.pstate_EXLOCK, rfl⟩
  have h_pstate_PAN : p_PAN = interpret rho.val caller.caller ⟨.pstate_PAN, rfl⟩ := actual ⟨.pstate_PAN, rfl⟩
  have h_pstate_UAO : p_UAO = interpret rho.val caller.caller ⟨.pstate_UAO, rfl⟩ := actual ⟨.pstate_UAO, rfl⟩
  have h_pstate_DIT : p_DIT = interpret rho.val caller.caller ⟨.pstate_DIT, rfl⟩ := actual ⟨.pstate_DIT, rfl⟩
  have h_pstate_TCO : p_TCO = interpret rho.val caller.caller ⟨.pstate_TCO, rfl⟩ := actual ⟨.pstate_TCO, rfl⟩
  have h_pstate_PM : p_PM = interpret rho.val caller.caller ⟨.pstate_PM, rfl⟩ := actual ⟨.pstate_PM, rfl⟩
  have h_pstate_PPEND : p_PPEND = interpret rho.val caller.caller ⟨.pstate_PPEND, rfl⟩ := actual ⟨.pstate_PPEND, rfl⟩
  have h_pstate_BTYPE : p_BTYPE = interpret rho.val caller.caller ⟨.pstate_BTYPE, rfl⟩ := actual ⟨.pstate_BTYPE, rfl⟩
  have h_pstate_ZA : p_ZA = interpret rho.val caller.caller ⟨.pstate_ZA, rfl⟩ := actual ⟨.pstate_ZA, rfl⟩
  have h_pstate_SM : p_SM = interpret rho.val caller.caller ⟨.pstate_SM, rfl⟩ := actual ⟨.pstate_SM, rfl⟩
  have h_pstate_ALLINT : p_ALLINT = interpret rho.val caller.caller ⟨.pstate_ALLINT, rfl⟩ := actual ⟨.pstate_ALLINT, rfl⟩
  have h_pstate_SS : p_SS = interpret rho.val caller.caller ⟨.pstate_SS, rfl⟩ := actual ⟨.pstate_SS, rfl⟩
  have h_pstate_IL : p_IL = interpret rho.val caller.caller ⟨.pstate_IL, rfl⟩ := actual ⟨.pstate_IL, rfl⟩
  have h_pstate_EL : p_EL = interpret rho.val caller.caller ⟨.pstate_EL, rfl⟩ := actual ⟨.pstate_EL, rfl⟩
  have h_pstate_nRW : p_nRW = interpret rho.val caller.caller ⟨.pstate_nRW, rfl⟩ := actual ⟨.pstate_nRW, rfl⟩
  have h_pstate_SP : p_SP = interpret rho.val caller.caller ⟨.pstate_SP, rfl⟩ := actual ⟨.pstate_SP, rfl⟩
  have h_pstate_Q : p_Q = interpret rho.val caller.caller ⟨.pstate_Q, rfl⟩ := actual ⟨.pstate_Q, rfl⟩
  have h_pstate_GE : p_GE = interpret rho.val caller.caller ⟨.pstate_GE, rfl⟩ := actual ⟨.pstate_GE, rfl⟩
  have h_pstate_SSBS : p_SSBS = interpret rho.val caller.caller ⟨.pstate_SSBS, rfl⟩ := actual ⟨.pstate_SSBS, rfl⟩
  have h_pstate_IT : p_IT = interpret rho.val caller.caller ⟨.pstate_IT, rfl⟩ := actual ⟨.pstate_IT, rfl⟩
  have h_pstate_J : p_J = interpret rho.val caller.caller ⟨.pstate_J, rfl⟩ := actual ⟨.pstate_J, rfl⟩
  have h_pstate_T : p_T = interpret rho.val caller.caller ⟨.pstate_T, rfl⟩ := actual ⟨.pstate_T, rfl⟩
  have h_pstate_E : p_E = interpret rho.val caller.caller ⟨.pstate_E, rfl⟩ := actual ⟨.pstate_E, rfl⟩
  have h_pstate_M : p_M = interpret rho.val caller.caller ⟨.pstate_M, rfl⟩ := actual ⟨.pstate_M, rfl⟩
  have h128 : r_bank_BitVec_128 = sourceBank128 rho caller ⟨r_gpr, r_SP_EL3, r_SP_EL2, r_SP_EL1, r_SP_EL0, r__ZT0, r__ZA, r__FFR, r__P, r__Z, r_PhysicalCount, r__PC, r_bank_BitVec_128 ._TTBR0_EL2, r_bank_BitVec_128 .TTBR1_EL2, r_bank_BitVec_64 .HTTBR, r_bank_BitVec_64⟩ := by
    funext key
    cases key <;> first | rfl | exact actual ⟨.bank_BitVec_128 _, rfl⟩
  have h64 : r_bank_BitVec_64 = sourceBank64 rho caller ⟨r_gpr, r_SP_EL3, r_SP_EL2, r_SP_EL1, r_SP_EL0, r__ZT0, r__ZA, r__FFR, r__P, r__Z, r_PhysicalCount, r__PC, r_bank_BitVec_128 ._TTBR0_EL2, r_bank_BitVec_128 .TTBR1_EL2, r_bank_BitVec_64 .HTTBR, r_bank_BitVec_64⟩ := by
    funext key
    by_cases h : isEntryData64 key = true
    · rw [sourceBank64_entry rho caller _ key h]; split <;> (subst_vars; rfl)
    · have h' := Bool.eq_false_iff.mpr h
      exact (actual ⟨.bank_BitVec_64 key, bank64_notData key h'⟩).trans (sourceBank64_ne rho caller _ key h').symm
  subst h___emulator_termination_opcode h_PMEVCNTSVR_EL1 h_SPESampleCounter h_SPERecordData h___mpam_vpmr_max h___BranchTaken h_Branchtypetaken h___ThisInstrEnc
  subst h___SPE_LFSR h_SPESampleOpType h_TSTATE h_FPSR h_FPCR h_BTypeCompatible h_BTypeNext h_RC
  subst h_ShouldAdvanceSS h_ShouldAdvanceIT h_PMULastThresholdValue h_PMUEventAccumulator h_VariantImplemented h_FeatureImpl h_bank_BitVec_32 h_bank_Vector_BitVec_32_16
  subst h_bank_Vector_BitVec_32_4 h_bank_Vector_BitVec_64_32 h_bank_Vector_BitVec_64_16 h_bank_Vector_BitVec_64_4 h_bank_Vector_BitVec_32_31 h_bank_Bool h_bank_Int h_bank_BitVec_1
  subst h_bank_BitVec_56 h_bank_BitVec_16 h_bank_BitVec_4 h_bank_Vector_Bool_32 h_bank_Vector_BitVec_64_64 h_bank_Option_InterruptID h_bank_BitVec_8 h_bank_BitVec_2
  subst h_bank_Vector_BitVec_64_7 h_bank_Signal h_pstate_N h_pstate_Z h_pstate_C h_pstate_V h_pstate_D h_pstate_A
  subst h_pstate_I h_pstate_F h_pstate_EXLOCK h_pstate_PAN h_pstate_UAO h_pstate_DIT h_pstate_TCO h_pstate_PM
  subst h_pstate_PPEND h_pstate_BTYPE h_pstate_ZA h_pstate_SM h_pstate_ALLINT h_pstate_SS h_pstate_IL h_pstate_EL
  subst h_pstate_nRW h_pstate_SP h_pstate_Q h_pstate_GE h_pstate_SSBS h_pstate_IT h_pstate_J h_pstate_T
  subst h_pstate_E h_pstate_M
  conv => lhs; rw [h128, h64]
  rfl

/-- Any register function of the actual entry is that function of the source register file. -/
theorem entry_function {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho}
    {result : Type} (f : ArmFull.Regs → result)
    (configuration : Configuration rho caller) (regs : ArmFull.Regs)
    (agreement : AgreesAt configuration regs) :
    f regs = f (sourceRegs rho caller (dataOf regs)) :=
  congrArg f (regs_eq_source configuration regs agreement)

end ReleaseProfile.GB10

#print axioms ReleaseProfile.GB10.regs_eq_source
#print axioms ReleaseProfile.GB10.entry_function
