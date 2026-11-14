import ReleaseProfile.GB10.FeatureSource
import ReleaseProfile.MachineSource.WordRecipe

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024

namespace ReleaseProfile.GB10

open ReleaseProfile.MachineSource

/-- Generic-timer registers that are per-entry DATA (next train, boss 820e): the seven timers' CTL/CVAL and
CNTHCTL_EL2. The positive C2 payload chooses them (quiet by construction); C1 keeps GB10.TimersQuiet named. -/
def isTimerData64 : ArmFull.Bank_BitVec_64 → Bool
  | .CNTP_CTL_EL0 => true
  | .CNTP_CVAL_EL0 => true
  | .CNTHP_CTL_EL2 => true
  | .CNTHP_CVAL_EL2 => true
  | .CNTHPS_CTL_EL2 => true
  | .CNTHPS_CVAL_EL2 => true
  | .CNTPS_CTL_EL1 => true
  | .CNTPS_CVAL_EL1 => true
  | .CNTV_CTL_EL0 => true
  | .CNTV_CVAL_EL0 => true
  | .CNTHV_CTL_EL2 => true
  | .CNTHV_CVAL_EL2 => true
  | .CNTHVS_CTL_EL2 => true
  | .CNTHVS_CVAL_EL2 => true
  | .CNTHCTL_EL2 => true
  | _ => false

/-- 64-bit bank keys that are entry data: the HTTBR page-table-root alias and the generic-timer registers. -/
def isEntryData64 (key : ArmFull.Bank_BitVec_64) : Bool :=
  key == .HTTBR || isTimerData64 key

/-- Initial conservative data exclusions. Remaining state/semantic-role refinements require review. -/
def isDataCoordinate : RawCoordinate → Bool
  | .gpr => true
  | .SP_EL3 => true
  | .SP_EL2 => true
  | .SP_EL1 => true
  | .SP_EL0 => true
  | ._ZT0 => true
  | ._ZA => true
  | ._FFR => true
  | ._P => true
  | ._Z => true
  | .PhysicalCount => true
  | ._PC => true
  | .bank_BitVec_128 ._TTBR0_EL2 => true
  | .bank_BitVec_128 .TTBR1_EL2 => true
  | .bank_BitVec_64 key => isEntryData64 key
  | _ => false

/-- Every non-data raw coordinate is represented; no remaining key silently defaults. -/
abbrev ProfileCoordinate := { c : RawCoordinate // isDataCoordinate c = false }

/-- Every 64-bit bank key that is not entry data (HTTBR, generic timers) is a profile coordinate. -/
theorem bank64_notData (key : ArmFull.Bank_BitVec_64) (h : isEntryData64 key = false) :
    isDataCoordinate (.bank_BitVec_64 key) = false := h

def isCallerCoordinate : RawCoordinate → Bool
  | .FPSR => true
  | .FPCR => true
  | .pstate_N => true
  | .pstate_Z => true
  | .pstate_C => true
  | .pstate_V => true
  | .pstate_D => true
  | .pstate_A => true
  | .pstate_I => true
  | .pstate_F => true
  | .pstate_EXLOCK => true
  | .pstate_PAN => true
  | .pstate_UAO => true
  | .pstate_DIT => true
  | .pstate_TCO => true
  | .pstate_PM => true
  | .pstate_PPEND => true
  | .pstate_BTYPE => true
  | .pstate_ZA => true
  | .pstate_SM => true
  | .pstate_ALLINT => true
  | .pstate_SS => true
  | .pstate_IL => true
  | .pstate_EL => true
  | .pstate_nRW => true
  | .pstate_SP => true
  | .pstate_Q => true
  | .pstate_GE => true
  | .pstate_SSBS => true
  | .pstate_IT => true
  | .pstate_J => true
  | .pstate_T => true
  | .pstate_E => true
  | .pstate_M => true
  | _ => false

/-- Explicit per-entry caller configuration, outside every model-witness existential. -/
structure Caller where
  pstate : ArmFull.ProcState
  fpcr : BitVec 64
  fpsr : BitVec 64

def Caller.read (caller : Caller) : (c : RawCoordinate) →
    isCallerCoordinate c = true → RawCoordinate.Value c
  | .gpr, impossible => False.elim (Bool.false_ne_true impossible)
  | .__emulator_termination_opcode, impossible => False.elim (Bool.false_ne_true impossible)
  | .PMEVCNTSVR_EL1, impossible => False.elim (Bool.false_ne_true impossible)
  | .SPESampleCounter, impossible => False.elim (Bool.false_ne_true impossible)
  | .SPERecordData, impossible => False.elim (Bool.false_ne_true impossible)
  | .SP_EL3, impossible => False.elim (Bool.false_ne_true impossible)
  | .SP_EL2, impossible => False.elim (Bool.false_ne_true impossible)
  | .SP_EL1, impossible => False.elim (Bool.false_ne_true impossible)
  | .SP_EL0, impossible => False.elim (Bool.false_ne_true impossible)
  | .__mpam_vpmr_max, impossible => False.elim (Bool.false_ne_true impossible)
  | .__BranchTaken, impossible => False.elim (Bool.false_ne_true impossible)
  | .Branchtypetaken, impossible => False.elim (Bool.false_ne_true impossible)
  | .__ThisInstrEnc, impossible => False.elim (Bool.false_ne_true impossible)
  | .__SPE_LFSR, impossible => False.elim (Bool.false_ne_true impossible)
  | .SPESampleOpType, impossible => False.elim (Bool.false_ne_true impossible)
  | .TSTATE, impossible => False.elim (Bool.false_ne_true impossible)
  | .FPSR, _ => caller.fpsr
  | .FPCR, _ => caller.fpcr
  | ._ZT0, impossible => False.elim (Bool.false_ne_true impossible)
  | ._ZA, impossible => False.elim (Bool.false_ne_true impossible)
  | ._FFR, impossible => False.elim (Bool.false_ne_true impossible)
  | ._P, impossible => False.elim (Bool.false_ne_true impossible)
  | ._Z, impossible => False.elim (Bool.false_ne_true impossible)
  | .BTypeCompatible, impossible => False.elim (Bool.false_ne_true impossible)
  | .BTypeNext, impossible => False.elim (Bool.false_ne_true impossible)
  | .RC, impossible => False.elim (Bool.false_ne_true impossible)
  | .PhysicalCount, impossible => False.elim (Bool.false_ne_true impossible)
  | ._PC, impossible => False.elim (Bool.false_ne_true impossible)
  | .ShouldAdvanceSS, impossible => False.elim (Bool.false_ne_true impossible)
  | .ShouldAdvanceIT, impossible => False.elim (Bool.false_ne_true impossible)
  | .pstate_N, _ => caller.pstate.N
  | .pstate_Z, _ => caller.pstate.Z
  | .pstate_C, _ => caller.pstate.C
  | .pstate_V, _ => caller.pstate.V
  | .pstate_D, _ => caller.pstate.D
  | .pstate_A, _ => caller.pstate.A
  | .pstate_I, _ => caller.pstate.I
  | .pstate_F, _ => caller.pstate.F
  | .pstate_EXLOCK, _ => caller.pstate.EXLOCK
  | .pstate_PAN, _ => caller.pstate.PAN
  | .pstate_UAO, _ => caller.pstate.UAO
  | .pstate_DIT, _ => caller.pstate.DIT
  | .pstate_TCO, _ => caller.pstate.TCO
  | .pstate_PM, _ => caller.pstate.PM
  | .pstate_PPEND, _ => caller.pstate.PPEND
  | .pstate_BTYPE, _ => caller.pstate.BTYPE
  | .pstate_ZA, _ => caller.pstate.ZA
  | .pstate_SM, _ => caller.pstate.SM
  | .pstate_ALLINT, _ => caller.pstate.ALLINT
  | .pstate_SS, _ => caller.pstate.SS
  | .pstate_IL, _ => caller.pstate.IL
  | .pstate_EL, _ => caller.pstate.EL
  | .pstate_nRW, _ => caller.pstate.nRW
  | .pstate_SP, _ => caller.pstate.SP
  | .pstate_Q, _ => caller.pstate.Q
  | .pstate_GE, _ => caller.pstate.GE
  | .pstate_SSBS, _ => caller.pstate.SSBS
  | .pstate_IT, _ => caller.pstate.IT
  | .pstate_J, _ => caller.pstate.J
  | .pstate_T, _ => caller.pstate.T
  | .pstate_E, _ => caller.pstate.E
  | .pstate_M, _ => caller.pstate.M
  | .PMULastThresholdValue, impossible => False.elim (Bool.false_ne_true impossible)
  | .PMUEventAccumulator, impossible => False.elim (Bool.false_ne_true impossible)
  | .VariantImplemented, impossible => False.elim (Bool.false_ne_true impossible)
  | .feature _, impossible => False.elim (Bool.false_ne_true impossible)
  | .bank_BitVec_32 _, impossible => False.elim (Bool.false_ne_true impossible)
  | .bank_Vector_BitVec_32_16 _, impossible => False.elim (Bool.false_ne_true impossible)
  | .bank_Vector_BitVec_32_4 _, impossible => False.elim (Bool.false_ne_true impossible)
  | .bank_Vector_BitVec_64_32 _, impossible => False.elim (Bool.false_ne_true impossible)
  | .bank_BitVec_64 _, impossible => False.elim (Bool.false_ne_true impossible)
  | .bank_Vector_BitVec_64_16 _, impossible => False.elim (Bool.false_ne_true impossible)
  | .bank_Vector_BitVec_64_4 _, impossible => False.elim (Bool.false_ne_true impossible)
  | .bank_Vector_BitVec_32_31 _, impossible => False.elim (Bool.false_ne_true impossible)
  | .bank_Bool _, impossible => False.elim (Bool.false_ne_true impossible)
  | .bank_Int _, impossible => False.elim (Bool.false_ne_true impossible)
  | .bank_BitVec_1 _, impossible => False.elim (Bool.false_ne_true impossible)
  | .bank_BitVec_56 _, impossible => False.elim (Bool.false_ne_true impossible)
  | .bank_BitVec_16 _, impossible => False.elim (Bool.false_ne_true impossible)
  | .bank_BitVec_4 _, impossible => False.elim (Bool.false_ne_true impossible)
  | .bank_BitVec_128 _, impossible => False.elim (Bool.false_ne_true impossible)
  | .bank_Vector_Bool_32 _, impossible => False.elim (Bool.false_ne_true impossible)
  | .bank_Vector_BitVec_64_64 _, impossible => False.elim (Bool.false_ne_true impossible)
  | .bank_Option_InterruptID _, impossible => False.elim (Bool.false_ne_true impossible)
  | .bank_BitVec_8 _, impossible => False.elim (Bool.false_ne_true impossible)
  | .bank_BitVec_2 _, impossible => False.elim (Bool.false_ne_true impossible)
  | .bank_Vector_BitVec_64_7 _, impossible => False.elim (Bool.false_ne_true impossible)
  | .bank_Signal _, impossible => False.elim (Bool.false_ne_true impossible)

/-- ControlRows ratified deployment obligation; an external obligation key, never a readback. -/
def ratified (row : String) : AuthorityRef := ⟨"D242/" ++ row, .ratifiedControl⟩

/-- D252 ratified deployment obligation (OS/firmware control), unattested until deploy-check/readback. -/
def ratifiedControlAtoms (row : String) : AuthorityRef := ⟨"D252/" ++ row, .ratifiedControl⟩

/-- D253 ratified deployment obligation (WXN/IPS/raw T0SZ), unattested until deploy-check/readback. -/
def ratifiedTranslationControls (row : String) : AuthorityRef := ⟨"D253/" ++ row, .ratifiedControl⟩

/-- D46 measured-config premise (Linux MAIR_EL1_SET), unattested until deploy-check/readback. -/
def ratified46 (row : String) : AuthorityRef := ⟨"D46/" ++ row, .ratifiedControl⟩

/-- Doug decision 33 (catalogue E3) SCTLR bits, unattested until deploy-check/readback. -/
def ratified33 (row : String) : AuthorityRef := ⟨"D33/" ++ row, .ratifiedControl⟩

/-- Doug D257 ratified deployment obligation (and boss-delegated D257/<field> settings). -/
def ratifiedAlignmentControl (row : String) : AuthorityRef := ⟨"D257/" ++ row, .ratifiedControl⟩

/-- Architectural RES0 because the governing feature is declared absent (TRM grade). -/
def trmRes0 (row : String) : AuthorityRef := ⟨"TRM-RES0/FEAT_GCS-absent/" ++ row, .rawTrm⟩

def isControlWord : ArmFull.Bank_BitVec_64 → Bool
  | .HCR_EL2 => true
  | .SCR_EL3 => true
  | .SCTLR_EL2 => true
  | .TCR_EL2 => true
  | .PMBLIMITR_EL1 => true
  | .MDSCR_EL1 => true
  | .BRBFCR_EL1 => true
  | .MDCR_EL3 => true
  | .PMINTENCLR_EL1 => true
  | .MAIR_EL2 => true
  | _ => false

theorem control_notEntry {key : ArmFull.Bank_BitVec_64} (control : isControlWord key = true) :
    isEntryData64 key = false := by
  revert control; cases key <;> decide

/-- Exactly the ControlRows ratified control bits. -/
def controlDeclared : ArmFull.Bank_BitVec_64 → Nat → Option (Bool × AuthorityRef)
  | .HCR_EL2, 34 => some (true, ratified "HCR_EL2.E2H")
  | .HCR_EL2, 27 => some (true, ratified "HCR_EL2.TGE")
  | .HCR_EL2, 31 => some (true, ratified "HCR_EL2.RW")
  | .SCR_EL3, 0 => some (true, ratified "SCR_EL3.NS")
  | .SCR_EL3, 10 => some (true, ratified "SCR_EL3.RW")
  | .SCR_EL3, 18 => some (false, ratified "SCR_EL3.EEL2")
  | .SCR_EL3, 62 => some (false, ratified "SCR_EL3.NSE")
  | .SCTLR_EL2, 25 => some (false, ratified "SCTLR_EL2.EE")
  | .SCTLR_EL2, 38 => some (false, ratified "SCTLR_EL2.TCF0[0]")
  | .SCTLR_EL2, 39 => some (false, ratified "SCTLR_EL2.TCF0[1]")
  | .TCR_EL2, 37 => some (true, ratified "TCR_EL2.TBI0")
  | .TCR_EL2, 51 => some (false, ratified "TCR_EL2.TBID0")
  | .TCR_EL2, 14 => some (false, ratified "TCR_EL2.TG0[0]")
  | .TCR_EL2, 15 => some (false, ratified "TCR_EL2.TG0[1]")
  | .SCTLR_EL2, 0 => some (true, ratifiedControlAtoms "SCTLR_EL2.M")
  | .SCTLR_EL2, 2 => some (true, ratifiedControlAtoms "SCTLR_EL2.C")
  | .SCTLR_EL2, 24 => some (false, ratifiedControlAtoms "SCTLR_EL2.E0E")
  | .TCR_EL2, 59 => some (false, ratifiedControlAtoms "TCR_EL2.DS")
  | .PMBLIMITR_EL1, 0 => some (false, ratifiedControlAtoms "PMBLIMITR_EL1.E")
  | .MDSCR_EL1, 0 => some (false, ratifiedControlAtoms "MDSCR_EL1.SS")
  | .MDSCR_EL1, 15 => some (false, ratifiedControlAtoms "MDSCR_EL1.MDE")
  | .BRBFCR_EL1, 7 => some (true, ratifiedControlAtoms "BRBFCR_EL1.PAUSED")
  | .MDCR_EL3, 12 => some (true, ratifiedControlAtoms "MDCR_EL3.NSPB[0]")
  | .MDCR_EL3, 13 => some (true, ratifiedControlAtoms "MDCR_EL3.NSPB[1]")
  | .MDCR_EL3, 11 => some (false, ratifiedControlAtoms "MDCR_EL3.NSPBE")
  | .PMINTENCLR_EL1, 0 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[0]")
  | .PMINTENCLR_EL1, 1 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[1]")
  | .PMINTENCLR_EL1, 2 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[2]")
  | .PMINTENCLR_EL1, 3 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[3]")
  | .PMINTENCLR_EL1, 4 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[4]")
  | .PMINTENCLR_EL1, 5 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[5]")
  | .PMINTENCLR_EL1, 6 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[6]")
  | .PMINTENCLR_EL1, 7 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[7]")
  | .PMINTENCLR_EL1, 8 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[8]")
  | .PMINTENCLR_EL1, 9 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[9]")
  | .PMINTENCLR_EL1, 10 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[10]")
  | .PMINTENCLR_EL1, 11 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[11]")
  | .PMINTENCLR_EL1, 12 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[12]")
  | .PMINTENCLR_EL1, 13 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[13]")
  | .PMINTENCLR_EL1, 14 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[14]")
  | .PMINTENCLR_EL1, 15 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[15]")
  | .PMINTENCLR_EL1, 16 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[16]")
  | .PMINTENCLR_EL1, 17 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[17]")
  | .PMINTENCLR_EL1, 18 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[18]")
  | .PMINTENCLR_EL1, 19 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[19]")
  | .PMINTENCLR_EL1, 20 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[20]")
  | .PMINTENCLR_EL1, 21 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[21]")
  | .PMINTENCLR_EL1, 22 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[22]")
  | .PMINTENCLR_EL1, 23 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[23]")
  | .PMINTENCLR_EL1, 24 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[24]")
  | .PMINTENCLR_EL1, 25 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[25]")
  | .PMINTENCLR_EL1, 26 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[26]")
  | .PMINTENCLR_EL1, 27 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[27]")
  | .PMINTENCLR_EL1, 28 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[28]")
  | .PMINTENCLR_EL1, 29 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[29]")
  | .PMINTENCLR_EL1, 30 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[30]")
  | .PMINTENCLR_EL1, 31 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[31]")
  | .PMINTENCLR_EL1, 32 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[32]")
  | .PMINTENCLR_EL1, 33 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[33]")
  | .PMINTENCLR_EL1, 34 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[34]")
  | .PMINTENCLR_EL1, 35 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[35]")
  | .PMINTENCLR_EL1, 36 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[36]")
  | .PMINTENCLR_EL1, 37 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[37]")
  | .PMINTENCLR_EL1, 38 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[38]")
  | .PMINTENCLR_EL1, 39 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[39]")
  | .PMINTENCLR_EL1, 40 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[40]")
  | .PMINTENCLR_EL1, 41 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[41]")
  | .PMINTENCLR_EL1, 42 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[42]")
  | .PMINTENCLR_EL1, 43 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[43]")
  | .PMINTENCLR_EL1, 44 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[44]")
  | .PMINTENCLR_EL1, 45 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[45]")
  | .PMINTENCLR_EL1, 46 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[46]")
  | .PMINTENCLR_EL1, 47 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[47]")
  | .PMINTENCLR_EL1, 48 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[48]")
  | .PMINTENCLR_EL1, 49 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[49]")
  | .PMINTENCLR_EL1, 50 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[50]")
  | .PMINTENCLR_EL1, 51 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[51]")
  | .PMINTENCLR_EL1, 52 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[52]")
  | .PMINTENCLR_EL1, 53 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[53]")
  | .PMINTENCLR_EL1, 54 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[54]")
  | .PMINTENCLR_EL1, 55 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[55]")
  | .PMINTENCLR_EL1, 56 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[56]")
  | .PMINTENCLR_EL1, 57 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[57]")
  | .PMINTENCLR_EL1, 58 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[58]")
  | .PMINTENCLR_EL1, 59 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[59]")
  | .PMINTENCLR_EL1, 60 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[60]")
  | .PMINTENCLR_EL1, 61 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[61]")
  | .PMINTENCLR_EL1, 62 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[62]")
  | .PMINTENCLR_EL1, 63 => some (false, ratifiedControlAtoms "PMINTENCLR_EL1[63]")
  | .SCTLR_EL2, 19 => some (false, ratifiedTranslationControls "SCTLR_EL2.WXN")
  | .TCR_EL2, 32 => some (false, ratifiedTranslationControls "TCR_EL2.IPS[0]")
  | .TCR_EL2, 33 => some (true, ratifiedTranslationControls "TCR_EL2.IPS[1]")
  | .TCR_EL2, 34 => some (false, ratifiedTranslationControls "TCR_EL2.IPS[2]")
  | .TCR_EL2, 0 => some (false, ratifiedTranslationControls "TCR_EL2.T0SZ[0]")
  | .TCR_EL2, 1 => some (false, ratifiedTranslationControls "TCR_EL2.T0SZ[1]")
  | .TCR_EL2, 2 => some (false, ratifiedTranslationControls "TCR_EL2.T0SZ[2]")
  | .TCR_EL2, 3 => some (false, ratifiedTranslationControls "TCR_EL2.T0SZ[3]")
  | .TCR_EL2, 4 => some (true, ratifiedTranslationControls "TCR_EL2.T0SZ[4]")
  | .TCR_EL2, 5 => some (false, ratifiedTranslationControls "TCR_EL2.T0SZ[5]")
  | .MAIR_EL2, 0 => some (true, ratified46 "MAIR_EL2[0]")
  | .MAIR_EL2, 1 => some (true, ratified46 "MAIR_EL2[1]")
  | .MAIR_EL2, 2 => some (true, ratified46 "MAIR_EL2[2]")
  | .MAIR_EL2, 3 => some (true, ratified46 "MAIR_EL2[3]")
  | .MAIR_EL2, 4 => some (true, ratified46 "MAIR_EL2[4]")
  | .MAIR_EL2, 5 => some (true, ratified46 "MAIR_EL2[5]")
  | .MAIR_EL2, 6 => some (true, ratified46 "MAIR_EL2[6]")
  | .MAIR_EL2, 7 => some (true, ratified46 "MAIR_EL2[7]")
  | .MAIR_EL2, 8 => some (true, ratified46 "MAIR_EL2[8]")
  | .MAIR_EL2, 9 => some (true, ratified46 "MAIR_EL2[9]")
  | .MAIR_EL2, 10 => some (true, ratified46 "MAIR_EL2[10]")
  | .MAIR_EL2, 11 => some (true, ratified46 "MAIR_EL2[11]")
  | .MAIR_EL2, 12 => some (true, ratified46 "MAIR_EL2[12]")
  | .MAIR_EL2, 13 => some (true, ratified46 "MAIR_EL2[13]")
  | .MAIR_EL2, 14 => some (true, ratified46 "MAIR_EL2[14]")
  | .MAIR_EL2, 15 => some (true, ratified46 "MAIR_EL2[15]")
  | .MAIR_EL2, 16 => some (false, ratified46 "MAIR_EL2[16]")
  | .MAIR_EL2, 17 => some (false, ratified46 "MAIR_EL2[17]")
  | .MAIR_EL2, 18 => some (true, ratified46 "MAIR_EL2[18]")
  | .MAIR_EL2, 19 => some (false, ratified46 "MAIR_EL2[19]")
  | .MAIR_EL2, 20 => some (false, ratified46 "MAIR_EL2[20]")
  | .MAIR_EL2, 21 => some (false, ratified46 "MAIR_EL2[21]")
  | .MAIR_EL2, 22 => some (true, ratified46 "MAIR_EL2[22]")
  | .MAIR_EL2, 23 => some (false, ratified46 "MAIR_EL2[23]")
  | .MAIR_EL2, 24 => some (false, ratified46 "MAIR_EL2[24]")
  | .MAIR_EL2, 25 => some (false, ratified46 "MAIR_EL2[25]")
  | .MAIR_EL2, 26 => some (false, ratified46 "MAIR_EL2[26]")
  | .MAIR_EL2, 27 => some (false, ratified46 "MAIR_EL2[27]")
  | .MAIR_EL2, 28 => some (false, ratified46 "MAIR_EL2[28]")
  | .MAIR_EL2, 29 => some (false, ratified46 "MAIR_EL2[29]")
  | .MAIR_EL2, 30 => some (false, ratified46 "MAIR_EL2[30]")
  | .MAIR_EL2, 31 => some (false, ratified46 "MAIR_EL2[31]")
  | .MAIR_EL2, 32 => some (false, ratified46 "MAIR_EL2[32]")
  | .MAIR_EL2, 33 => some (false, ratified46 "MAIR_EL2[33]")
  | .MAIR_EL2, 34 => some (true, ratified46 "MAIR_EL2[34]")
  | .MAIR_EL2, 35 => some (false, ratified46 "MAIR_EL2[35]")
  | .MAIR_EL2, 36 => some (false, ratified46 "MAIR_EL2[36]")
  | .MAIR_EL2, 37 => some (false, ratified46 "MAIR_EL2[37]")
  | .MAIR_EL2, 38 => some (false, ratified46 "MAIR_EL2[38]")
  | .MAIR_EL2, 39 => some (false, ratified46 "MAIR_EL2[39]")
  | .MAIR_EL2, 40 => some (false, ratified46 "MAIR_EL2[40]")
  | .MAIR_EL2, 41 => some (false, ratified46 "MAIR_EL2[41]")
  | .MAIR_EL2, 42 => some (false, ratified46 "MAIR_EL2[42]")
  | .MAIR_EL2, 43 => some (false, ratified46 "MAIR_EL2[43]")
  | .MAIR_EL2, 44 => some (false, ratified46 "MAIR_EL2[44]")
  | .MAIR_EL2, 45 => some (false, ratified46 "MAIR_EL2[45]")
  | .MAIR_EL2, 46 => some (false, ratified46 "MAIR_EL2[46]")
  | .MAIR_EL2, 47 => some (false, ratified46 "MAIR_EL2[47]")
  | .MAIR_EL2, 48 => some (false, ratified46 "MAIR_EL2[48]")
  | .MAIR_EL2, 49 => some (false, ratified46 "MAIR_EL2[49]")
  | .MAIR_EL2, 50 => some (false, ratified46 "MAIR_EL2[50]")
  | .MAIR_EL2, 51 => some (false, ratified46 "MAIR_EL2[51]")
  | .MAIR_EL2, 52 => some (false, ratified46 "MAIR_EL2[52]")
  | .MAIR_EL2, 53 => some (false, ratified46 "MAIR_EL2[53]")
  | .MAIR_EL2, 54 => some (false, ratified46 "MAIR_EL2[54]")
  | .MAIR_EL2, 55 => some (false, ratified46 "MAIR_EL2[55]")
  | .MAIR_EL2, 56 => some (false, ratified46 "MAIR_EL2[56]")
  | .MAIR_EL2, 57 => some (false, ratified46 "MAIR_EL2[57]")
  | .MAIR_EL2, 58 => some (false, ratified46 "MAIR_EL2[58]")
  | .MAIR_EL2, 59 => some (false, ratified46 "MAIR_EL2[59]")
  | .MAIR_EL2, 60 => some (false, ratified46 "MAIR_EL2[60]")
  | .MAIR_EL2, 61 => some (false, ratified46 "MAIR_EL2[61]")
  | .MAIR_EL2, 62 => some (false, ratified46 "MAIR_EL2[62]")
  | .MAIR_EL2, 63 => some (false, ratified46 "MAIR_EL2[63]")
  | .SCTLR_EL2, 12 => some (true, ratified33 "SCTLR_EL2.I")
  | .SCTLR_EL2, 3 => some (true, ratified33 "SCTLR_EL2.SA")
  | .SCTLR_EL2, 4 => some (true, ratified33 "SCTLR_EL2.SA0")
  | .SCTLR_EL2, 16 => some (false, ratified33 "SCTLR_EL2.nTWI")
  | .SCTLR_EL2, 18 => some (true, ratified33 "SCTLR_EL2.nTWE")
  | .SCTLR_EL2, 14 => some (true, ratified33 "SCTLR_EL2.DZE")
  | .SCTLR_EL2, 1 => some (false, ratifiedAlignmentControl "SCTLR_EL2.A")
  | .TCR_EL2, 7 => some (false, ratifiedAlignmentControl "TCR_EL2.EPD0")
  | .TCR_EL2, 41 => some (false, ratifiedAlignmentControl "TCR_EL2.HPD0")
  | .TCR_EL2, 53 => some (false, ratifiedAlignmentControl "TCR_EL2.NFD0")
  | .TCR_EL2, 60 => some (false, ratifiedAlignmentControl "TCR_EL2.MTX0")
  | .TCR_EL2, 55 => some (false, ratifiedAlignmentControl "TCR_EL2.E0PD0")
  | .TCR_EL2, 39 => some (true, ratifiedAlignmentControl "TCR_EL2.HA")
  | .TCR_EL2, 40 => some (true, ratifiedAlignmentControl "TCR_EL2.HD")
  | .TCR_EL2, 12 => some (true, ratifiedAlignmentControl "TCR_EL2.SH0[0]")
  | .TCR_EL2, 13 => some (true, ratifiedAlignmentControl "TCR_EL2.SH0[1]")
  | .TCR_EL2, 8 => some (true, ratifiedAlignmentControl "TCR_EL2.IRGN0[0]")
  | .TCR_EL2, 9 => some (false, ratifiedAlignmentControl "TCR_EL2.IRGN0[1]")
  | .TCR_EL2, 10 => some (true, ratifiedAlignmentControl "TCR_EL2.ORGN0[0]")
  | .TCR_EL2, 11 => some (false, ratifiedAlignmentControl "TCR_EL2.ORGN0[1]")
  | .SCR_EL3, 39 => some (false, trmRes0 "SCR_EL3.GCSEn")
  | _, _ => none

/-- No pending control symbols remain after D253; kept as an explicit empty table. -/
def controlPending : ArmFull.Bank_BitVec_64 → Nat → Option String
  | _, _ => none

#check "CURRENT_DECL GB10.controlBit"
/-- Per-bit control recipe: declared ratified bit or typed unresolved symbol; no old initializer. -/
def controlBit (key : ArmFull.Bank_BitVec_64) (index : Fin 64) : Slot Bool :=
  match controlDeclared key index.val with
  | some (value, authority) => .literal value authority
  | none =>
      match controlPending key index.val with
      | some symbol => .unresolved symbol
      | none => .unresolved (RawCoordinate.id (.bank_BitVec_64 key) ++ "[" ++ toString index.val ++ "]")

theorem controlBit_no_caller (key : ArmFull.Bank_BitVec_64) (index : Fin 64) :
    Slot.isCaller (controlBit key index) = false := by
  unfold controlBit
  split
  · rfl
  · split <;> rfl

def controlNoCaller (key : ArmFull.Bank_BitVec_64) : CallerValues (controlBit key) :=
  fun index impossible =>
    False.elim (Bool.false_ne_true ((controlBit_no_caller key index).symm.trans impossible))

def isControlWord32 : ArmFull.Bank_BitVec_32 → Bool
  | .EDECR => true
  | .CTIDEVCTL => true
  | ._EDSCR => true
  | .CNTCR => true
  | _ => false

def controlDeclared32 : ArmFull.Bank_BitVec_32 → Nat → Option (Bool × AuthorityRef)
  | .EDECR, 1 => some (false, ratifiedControlAtoms "EDECR.RCE")
  | .CTIDEVCTL, 1 => some (false, ratifiedControlAtoms "CTIDEVCTL.RCE")
  | ._EDSCR, 14 => some (false, ratifiedControlAtoms "EDSCR.HDE")
  | .CNTCR, 2 => some (false, ratifiedControlAtoms "CNTCR.SCEN")
  | _, _ => none

def controlBit32 (key : ArmFull.Bank_BitVec_32) (index : Fin 32) : Slot Bool :=
  match controlDeclared32 key index.val with
  | some (value, authority) => .literal value authority
  | none => .unresolved (RawCoordinate.id (.bank_BitVec_32 key) ++ "[" ++ toString index.val ++ "]")

theorem controlBit32_no_caller (key : ArmFull.Bank_BitVec_32) (index : Fin 32) :
    Slot.isCaller (controlBit32 key index) = false := by
  unfold controlBit32
  split <;> rfl

def controlNoCaller32 (key : ArmFull.Bank_BitVec_32) : CallerValues (controlBit32 key) :=
  fun index impossible =>
    False.elim (Bool.false_ne_true ((controlBit32_no_caller key index).symm.trans impossible))

/-- Finite registered source grammar. A feature-bank alias carries its actual identity equation. -/
inductive CoordinateRule : RawCoordinate → Type where
  | literal (c : RawCoordinate) (value : RawCoordinate.Value c) (authority : AuthorityRef) : CoordinateRule c
  | unresolved (c : RawCoordinate) (symbolKey : String) : CoordinateRule c
  | caller (c : RawCoordinate) (slot : isCallerCoordinate c = true) : CoordinateRule c
  | data (c : RawCoordinate) (slot : isDataCoordinate c = true) : CoordinateRule c
  | feature (index : Fin 259) : CoordinateRule (.feature index)
  | featureBank (bank : ArmFull.Bank_Bool) (index : Fin 259)
      (identity : FeatureSource.bankAlias bank = some index) : CoordinateRule (.bank_Bool bank)
  | control (key : ArmFull.Bank_BitVec_64) (slot : isControlWord key = true) :
      CoordinateRule (.bank_BitVec_64 key)
  | control32 (key : ArmFull.Bank_BitVec_32) (slot : isControlWord32 key = true) :
      CoordinateRule (.bank_BitVec_32 key)

def CoordinateRule.isUnresolved {c : RawCoordinate} : CoordinateRule c → Bool
  | .unresolved _ _ => true
  | _ => false

private def coordinateRules (c : RawCoordinate) : CoordinateRule c :=
  if data : isDataCoordinate c = true then .data c data else
  if caller : isCallerCoordinate c = true then .caller c caller else
  match c with
  | .feature index => .feature index
  | .bank_Bool bank =>
      match identity : FeatureSource.bankAlias bank with
      | some index => .featureBank bank index identity
      | none => .unresolved (.bank_Bool bank) (RawCoordinate.id (.bank_Bool bank))
  | .bank_Int .__supported_pa_size =>
      .literal (.bank_Int .__supported_pa_size) (40 : Int)
        ⟨"GB10-TABLE-D244/hardware/pa_bits", .rawTrm⟩
  | .bank_BitVec_64 key =>
      if control : isControlWord key = true then .control key control
      else .unresolved (.bank_BitVec_64 key) (RawCoordinate.id (.bank_BitVec_64 key))
  | .bank_BitVec_32 key =>
      if control : isControlWord32 key = true then .control32 key control
      else .unresolved (.bank_BitVec_32 key) (RawCoordinate.id (.bank_BitVec_32 key))
  | .bank_Int .NUM_BREAKPOINTS =>
      .literal (.bank_Int .NUM_BREAKPOINTS) (6 : Int) ⟨"GB10-TRM/x925:6119,a725:5371/breakpoints", .rawTrm⟩
  | .bank_Int .NUM_WATCHPOINTS =>
      .literal (.bank_Int .NUM_WATCHPOINTS) (4 : Int) ⟨"GB10-TRM/x925:6119,a725:5371/watchpoints", .rawTrm⟩
  | .bank_Int .__num_ctx_breakpoints =>
      .literal (.bank_Int .__num_ctx_breakpoints) (2 : Int) ⟨"GB10-TRM/x925:23536-23538,a725:24056-24059/CTX_CMPs", .rawTrm⟩
  | .bank_Int .__block_bbm_implemented =>
      .literal (.bank_Int .__block_bbm_implemented) (2 : Int) ⟨"GB10-TRM/x925:24920,a725:25379/ID_AA64MMFR2_EL1.BBM=0b0010", .rawTrm⟩
  | c => .unresolved c (RawCoordinate.id c)

/-- Source data contains actual typed recipes, not only a machine label or fingerprint. -/
structure SourceDescription where
  private mk ::
  features : Fin 259 → Slot Bool
  coordinates : (c : RawCoordinate) → CoordinateRule c

#check "CURRENT_DECL GB10.canonicalSource"
/-- The single registered VALUE used by this module; no API quantifies over another source. -/
def canonicalSource : SourceDescription :=
  ⟨FeatureSource.recipe, coordinateRules⟩

theorem canonical_feature_recipe : canonicalSource.features = FeatureSource.recipe := rfl

abbrev RawUnknowns := (c : RawCoordinate) →
  (canonicalSource.coordinates c).isUnresolved = true → RawCoordinate.Value c

/-- Core type executing the invocation (GB10 has both); a typed unknown, never chosen by a proof. -/
inductive CoreKind where
  | x925
  | a725
  deriving DecidableEq, Repr

structure Unknowns where
  features : UnknownValues canonicalSource.features
  registers : RawUnknowns
  controls : (key : ArmFull.Bank_BitVec_64) → UnknownValues (controlBit key)
  controls32 : (key : ArmFull.Bank_BitVec_32) → UnknownValues (controlBit32 key)
  coreKind : CoreKind

private def interpretRule (unknowns : Unknowns) (caller : Caller) :
    {c : RawCoordinate} → (rule : CoordinateRule c) →
    canonicalSource.coordinates c = rule → isDataCoordinate c = false → RawCoordinate.Value c
  | _, .literal _ value _, _, _ => value
  | c, .unresolved _ _, ruleIdentity, _ =>
      unknowns.registers c (by rw [ruleIdentity]; rfl)
  | c, .caller _ slot, _, _ => caller.read c slot
  | _, .data _ slot, _, notData =>
      False.elim (Bool.false_ne_true (notData.symm.trans slot))
  | _, .feature index, _, _ => FeatureSource.value unknowns.features index
  | _, .featureBank _ index _, _, _ => FeatureSource.value unknowns.features index
  | _, .control key _, _, _ =>
      WordRecipe.evaluate (controlBit key) (unknowns.controls key) (controlNoCaller key)
  | _, .control32 key _, _, _ =>
      WordRecipe.evaluate (controlBit32 key) (unknowns.controls32 key) (controlNoCaller32 key)

def interpret (unknowns : Unknowns) (caller : Caller) (c : ProfileCoordinate) :
    RawCoordinate.Value c.val :=
  interpretRule unknowns caller (canonicalSource.coordinates c.val) rfl c.property

/-- A registered nonconfiguration update has an explicit complete profile frame. -/
def updateGpr (regs : ArmFull.Regs) (gpr : Vector (BitVec 64) 31) : ArmFull.Regs :=
  { regs with gpr := gpr }

theorem updateGpr_frame (regs : ArmFull.Regs) (gpr : Vector (BitVec 64) 31)
    (c : ProfileCoordinate) :
    RawCoordinate.read (updateGpr regs gpr) c.val = RawCoordinate.read regs c.val := by
  rcases c with ⟨c, notData⟩
  cases c <;> first | rfl | cases notData

theorem interpret_feature (unknowns : Unknowns) (caller : Caller) (index : Fin 259) :
    interpret unknowns caller ⟨.feature index, rfl⟩ =
      FeatureSource.value unknowns.features index := rfl

theorem interpret_pa_bits (unknowns : Unknowns) (caller : Caller) :
    interpret unknowns caller ⟨.bank_Int .__supported_pa_size, rfl⟩ = (40 : Int) := rfl

theorem interpret_caller_el (unknowns : Unknowns) (caller : Caller) :
    interpret unknowns caller ⟨.pstate_EL, rfl⟩ = caller.pstate.EL := rfl

theorem interpret_caller_fpcr (unknowns : Unknowns) (caller : Caller) :
    interpret unknowns caller ⟨.FPCR, rfl⟩ = caller.fpcr := rfl

private theorem interpretRule_caller_independent (unknowns : Unknowns) (caller1 caller2 : Caller)
    {c : RawCoordinate} (rule : CoordinateRule c)
    (identity : canonicalSource.coordinates c = rule)
    (notData : isDataCoordinate c = false) (notCaller : isCallerCoordinate c = false) :
    interpretRule unknowns caller1 rule identity notData =
      interpretRule unknowns caller2 rule identity notData := by
  cases rule <;> try rfl
  rename_i slot
  exact False.elim (Bool.false_ne_true (notCaller.symm.trans slot))

theorem interpret_caller_independent (unknowns : Unknowns) (caller1 caller2 : Caller)
    (c : ProfileCoordinate) (notCaller : isCallerCoordinate c.val = false) :
    interpret unknowns caller1 c = interpret unknowns caller2 c := by
  exact interpretRule_caller_independent unknowns caller1 caller2
    (canonicalSource.coordinates c.val) rfl c.property notCaller

/-- Rule identity of each registered control word (concrete kernel reduction). -/
theorem coordinates_HCR_EL2 : canonicalSource.coordinates (.bank_BitVec_64 .HCR_EL2) = .control .HCR_EL2 rfl := rfl

theorem coordinates_SCR_EL3 : canonicalSource.coordinates (.bank_BitVec_64 .SCR_EL3) = .control .SCR_EL3 rfl := rfl

theorem coordinates_SCTLR_EL2 : canonicalSource.coordinates (.bank_BitVec_64 .SCTLR_EL2) = .control .SCTLR_EL2 rfl := rfl

theorem coordinates_TCR_EL2 : canonicalSource.coordinates (.bank_BitVec_64 .TCR_EL2) = .control .TCR_EL2 rfl := rfl

theorem coordinates_PMBLIMITR_EL1 : canonicalSource.coordinates (.bank_BitVec_64 .PMBLIMITR_EL1) = .control .PMBLIMITR_EL1 rfl := rfl

theorem coordinates_MDSCR_EL1 : canonicalSource.coordinates (.bank_BitVec_64 .MDSCR_EL1) = .control .MDSCR_EL1 rfl := rfl

theorem coordinates_BRBFCR_EL1 : canonicalSource.coordinates (.bank_BitVec_64 .BRBFCR_EL1) = .control .BRBFCR_EL1 rfl := rfl

theorem coordinates_MDCR_EL3 : canonicalSource.coordinates (.bank_BitVec_64 .MDCR_EL3) = .control .MDCR_EL3 rfl := rfl

theorem coordinates_PMINTENCLR_EL1 : canonicalSource.coordinates (.bank_BitVec_64 .PMINTENCLR_EL1) = .control .PMINTENCLR_EL1 rfl := rfl

theorem coordinates_MAIR_EL2 : canonicalSource.coordinates (.bank_BitVec_64 .MAIR_EL2) = .control .MAIR_EL2 rfl := rfl

theorem coordinates32_EDECR : canonicalSource.coordinates (.bank_BitVec_32 .EDECR) = .control32 .EDECR rfl := rfl

theorem coordinates32_CTIDEVCTL : canonicalSource.coordinates (.bank_BitVec_32 .CTIDEVCTL) = .control32 .CTIDEVCTL rfl := rfl

theorem coordinates32__EDSCR : canonicalSource.coordinates (.bank_BitVec_32 ._EDSCR) = .control32 ._EDSCR rfl := rfl

theorem coordinates32_CNTCR : canonicalSource.coordinates (.bank_BitVec_32 .CNTCR) = .control32 .CNTCR rfl := rfl

theorem interpret_trm_NUM_BREAKPOINTS (unknowns : Unknowns) (caller : Caller) :
    interpret unknowns caller ⟨.bank_Int .NUM_BREAKPOINTS, rfl⟩ = (6 : Int) := rfl

theorem interpret_trm_NUM_WATCHPOINTS (unknowns : Unknowns) (caller : Caller) :
    interpret unknowns caller ⟨.bank_Int .NUM_WATCHPOINTS, rfl⟩ = (4 : Int) := rfl

theorem interpret_trm___num_ctx_breakpoints (unknowns : Unknowns) (caller : Caller) :
    interpret unknowns caller ⟨.bank_Int .__num_ctx_breakpoints, rfl⟩ = (2 : Int) := rfl

theorem interpret_trm___block_bbm_implemented (unknowns : Unknowns) (caller : Caller) :
    interpret unknowns caller ⟨.bank_Int .__block_bbm_implemented, rfl⟩ = (2 : Int) := rfl

theorem coordinates_control (key : ArmFull.Bank_BitVec_64) (control : isControlWord key = true) :
    canonicalSource.coordinates (.bank_BitVec_64 key) = .control key control := by
  show coordinateRules (.bank_BitVec_64 key) = _
  unfold coordinateRules
  simp only [bank64_notData key (control_notEntry control), isCallerCoordinate, Bool.false_eq_true, ↓reduceDIte, control]

theorem coordinates_control32 (key : ArmFull.Bank_BitVec_32) (control : isControlWord32 key = true) :
    canonicalSource.coordinates (.bank_BitVec_32 key) = .control32 key control := by
  show coordinateRules (.bank_BitVec_32 key) = _
  unfold coordinateRules
  simp only [isDataCoordinate, isCallerCoordinate, Bool.false_eq_true, ↓reduceDIte, control]

theorem interpret_control32 (unknowns : Unknowns) (caller : Caller) (key : ArmFull.Bank_BitVec_32)
    (control : isControlWord32 key = true)
    (identity : canonicalSource.coordinates (.bank_BitVec_32 key) = .control32 key control) :
    interpret unknowns caller ⟨.bank_BitVec_32 key, rfl⟩ =
      WordRecipe.evaluate (controlBit32 key) (unknowns.controls32 key) (controlNoCaller32 key) := by
  have general : ∀ (rule : CoordinateRule (.bank_BitVec_32 key))
      (ruleIdentity : canonicalSource.coordinates (.bank_BitVec_32 key) = rule)
      (notData : isDataCoordinate (.bank_BitVec_32 key) = false),
      rule = .control32 key control →
      interpretRule unknowns caller rule ruleIdentity notData =
        WordRecipe.evaluate (controlBit32 key) (unknowns.controls32 key) (controlNoCaller32 key) := by
    intro rule ruleIdentity notData same
    subst same
    rfl
  exact general _ rfl rfl identity

theorem interpret_control32_declared (unknowns : Unknowns) (caller : Caller)
    (key : ArmFull.Bank_BitVec_32) (control : isControlWord32 key = true)
    (identity : canonicalSource.coordinates (.bank_BitVec_32 key) = .control32 key control)
    (index : Fin 32) (expected : Bool) (authority : AuthorityRef)
    (record : controlDeclared32 key index.val = some (expected, authority)) :
    (interpret unknowns caller ⟨.bank_BitVec_32 key, rfl⟩).getLsbD index.val = expected := by
  rw [interpret_control32 unknowns caller key control identity]
  apply WordRecipe.declared_bit _ _ _ index expected authority
  simp only [controlBit32, record]

theorem interpret_control32_unresolved (unknowns : Unknowns) (caller : Caller)
    (key : ArmFull.Bank_BitVec_32) (control : isControlWord32 key = true)
    (identity : canonicalSource.coordinates (.bank_BitVec_32 key) = .control32 key control)
    (index : Fin 32) (notDeclared : controlDeclared32 key index.val = none) :
    (interpret unknowns caller ⟨.bank_BitVec_32 key, rfl⟩).getLsbD index.val =
      unknowns.controls32 key index (by simp only [controlBit32, notDeclared, Slot.isUnknown]) := by
  rw [interpret_control32 unknowns caller key control identity]
  apply WordRecipe.unresolved_bit _ _ _ index
  simp only [controlBit32, notDeclared]
  rfl

theorem interpret_control (unknowns : Unknowns) (caller : Caller) (key : ArmFull.Bank_BitVec_64)
    (control : isControlWord key = true)
    (identity : canonicalSource.coordinates (.bank_BitVec_64 key) = .control key control) :
    interpret unknowns caller ⟨.bank_BitVec_64 key, bank64_notData key (control_notEntry control)⟩ =
      WordRecipe.evaluate (controlBit key) (unknowns.controls key) (controlNoCaller key) := by
  have general : ∀ (rule : CoordinateRule (.bank_BitVec_64 key))
      (ruleIdentity : canonicalSource.coordinates (.bank_BitVec_64 key) = rule)
      (notData : isDataCoordinate (.bank_BitVec_64 key) = false),
      rule = .control key control →
      interpretRule unknowns caller rule ruleIdentity notData =
        WordRecipe.evaluate (controlBit key) (unknowns.controls key) (controlNoCaller key) := by
    intro rule ruleIdentity notData same
    subst same
    rfl
  exact general _ rfl _ identity

theorem interpret_control_declared (unknowns : Unknowns) (caller : Caller)
    (key : ArmFull.Bank_BitVec_64) (control : isControlWord key = true)
    (identity : canonicalSource.coordinates (.bank_BitVec_64 key) = .control key control)
    (index : Fin 64) (expected : Bool) (authority : AuthorityRef)
    (record : controlDeclared key index.val = some (expected, authority)) :
    (interpret unknowns caller ⟨.bank_BitVec_64 key, bank64_notData key (control_notEntry control)⟩).getLsbD index.val = expected := by
  rw [interpret_control unknowns caller key control identity]
  apply WordRecipe.declared_bit _ _ _ index expected authority
  simp only [controlBit, record]

theorem interpret_control_pending (unknowns : Unknowns) (caller : Caller)
    (key : ArmFull.Bank_BitVec_64) (control : isControlWord key = true)
    (identity : canonicalSource.coordinates (.bank_BitVec_64 key) = .control key control)
    (index : Fin 64) (symbol : String)
    (notDeclared : controlDeclared key index.val = none)
    (record : controlPending key index.val = some symbol) :
    (interpret unknowns caller ⟨.bank_BitVec_64 key, bank64_notData key (control_notEntry control)⟩).getLsbD index.val =
      unknowns.controls key index (by simp only [controlBit, notDeclared, record, Slot.isUnknown]) := by
  rw [interpret_control unknowns caller key control identity]
  apply WordRecipe.unresolved_bit _ _ _ index symbol
  simp only [controlBit, notDeclared, record]

theorem coordinates_bank (bank : ArmFull.Bank_Bool) (index : Fin 259)
    (alias : FeatureSource.bankAlias bank = some index) :
    canonicalSource.coordinates (.bank_Bool bank) = .featureBank bank index alias := by
  show coordinateRules (.bank_Bool bank) = _
  unfold coordinateRules
  simp only [isDataCoordinate, isCallerCoordinate, Bool.false_eq_true, ↓reduceDIte]
  split
  · rename_i index2 alias2
    have same : some index = some index2 := alias.symm.trans alias2
    cases same
    rfl
  · rename_i none2
    cases alias.symm.trans none2

theorem interpret_feature_bank (unknowns : Unknowns) (caller : Caller)
    (bank : ArmFull.Bank_Bool) (index : Fin 259) (alias : FeatureSource.bankAlias bank = some index) :
    interpret unknowns caller ⟨.bank_Bool bank, rfl⟩ = FeatureSource.value unknowns.features index := by
  have general : ∀ (rule : CoordinateRule (.bank_Bool bank))
      (ruleIdentity : canonicalSource.coordinates (.bank_Bool bank) = rule)
      (notData : isDataCoordinate (.bank_Bool bank) = false),
      rule = .featureBank bank index alias →
      interpretRule unknowns caller rule ruleIdentity notData =
        FeatureSource.value unknowns.features index := by
    intro rule ruleIdentity notData same
    subst same
    rfl
  exact general _ rfl rfl (coordinates_bank bank index alias)

abbrev CommonCoordinate := { c : ProfileCoordinate // isCallerCoordinate c.val = false }

/-- Shared source views exclude caller-local PSTATE/FP values, rather than equating entire states. -/
def commonView (unknowns : Unknowns) (caller : Caller) (c : CommonCoordinate) :
    RawCoordinate.Value c.val.val := interpret unknowns caller c.val

theorem commonView_exact (unknowns : Unknowns) (caller1 caller2 : Caller) :
    commonView unknowns caller1 = commonView unknowns caller2 := by
  funext c
  exact interpret_caller_independent unknowns caller1 caller2 c.val c.property

end ReleaseProfile.GB10

#print axioms ReleaseProfile.GB10.canonical_feature_recipe
#print axioms ReleaseProfile.GB10.updateGpr_frame
#print axioms ReleaseProfile.GB10.interpret_feature
#print axioms ReleaseProfile.GB10.interpret_pa_bits
#print axioms ReleaseProfile.GB10.interpret_caller_el
#print axioms ReleaseProfile.GB10.interpret_caller_fpcr
#print axioms ReleaseProfile.GB10.interpret_caller_independent
#print axioms ReleaseProfile.GB10.commonView_exact
#print axioms ReleaseProfile.GB10.controlBit_no_caller
#print axioms ReleaseProfile.GB10.coordinates_bank
#print axioms ReleaseProfile.GB10.interpret_feature_bank
#print axioms ReleaseProfile.GB10.interpret_control
#print axioms ReleaseProfile.GB10.interpret_control_declared
#print axioms ReleaseProfile.GB10.interpret_control_pending
