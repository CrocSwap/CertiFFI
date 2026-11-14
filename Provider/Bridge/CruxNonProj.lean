import Bridge.CruxCore
import Bridge.NonProjRegs
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxNonProj
open ArmBridge.CruxCore ArmCertCT.CT2

/-- Bookkeeping bank keys of the heap model step: exactly the E20 and E22
    premise write sets plus the model-step bookkeeping writes (write-site table in CRUX-BKKEYS.md):
    SEE (writeReg SEE -1 / K), __clock_divider / __last_cycle_count / __cycle_count (cycle counter),
    __ThisInstr + __currentCond (__SetThisInstrDetails), _EDSCR + MDCCSR_EL0 (PipeAdv / bits 30:29), InGuardedPage (IFETCH +
    epilogue), __ExclusiveMonitorSet (prelude), __InstructionStep (fetch wrapper). -/
def bkHeap : BkKeys where
  b32 := fun k => match k with
    | .CNTP_CTL_S | ._CNTHP_CTL | ._CNTP_CTL_NS | ._EDSCR | .__ThisInstr => true | _ => false
  v32_16 := fun _ => false
  v32_4 := fun _ => false
  v64_32 := fun k => match k with | .PMEVCNTR_EL0 => true | _ => false
  b64 := fun k => match k with
    | .PMCCNTR_EL0 | .PMICNTR_EL0 | .PMOVSSET_EL0 | .PMOVSCLR_EL0 | .BRBTS_EL1
    | .CNTP_CTL_EL0 | .CNTV_CTL_EL0 | .CNTHP_CTL_EL2 | .CNTHV_CTL_EL2 | .CNTHPS_CTL_EL2 | .CNTHVS_CTL_EL2
    | .CNTPS_CTL_EL1 | .MDCCSR_EL0
    | .SPESamplePreviousBranchAddress => true
    | _ => false
  v64_16 := fun _ => false
  v64_4 := fun _ => false
  v32_31 := fun _ => false
  bool := fun k => match k with
    | .InGuardedPage | .__ExclusiveMonitorSet | .__InstructionStep | .SPESamplePreviousBranchAddressValid => true
    | _ => false
  int := fun k => match k with | .SEE | .__clock_divider | .__last_cycle_count | .__cycle_count => true | _ => false
  b1 := fun k => match k with | .EventRegister => true | _ => false
  b56 := fun _ => false
  b16 := fun _ => false
  b4 := fun k => match k with | .__currentCond => true | _ => false
  b128 := fun _ => false
  vbool32 := fun _ => false
  v64_64 := fun _ => false
  irq := fun k => match k with | .__GIC_Pending => true | _ => false
  b8 := fun _ => false
  b2 := fun _ => false
  v64_7 := fun _ => false
  signal := fun _ => false

/-- Setting a bookkeeping key is invisible to the mask. -/
theorem maskBank_set {κ α : Type} [Inhabited α] [DecidableEq κ] (bk : κ → Bool) (m : κ → α) (k : κ) (v : α)
    (hk : bk k = true) : maskBank bk (RegMap.set m k v) = maskBank bk m := by
  funext j
  unfold maskBank
  by_cases h : j = k
  · subst h; simp [hk]
  · simp [Sail.ConcurrencyInterfaceV1.RegMap.set_ne _ _ h]

theorem mask_erase20 (x : Regs) : mask bkHeap (eraseE20 x) = mask bkHeap x := by
  unfold mask eraseE20
  simp (disch := decide) only [maskBank_set]

theorem mask_erase22 (x : Regs) : mask bkHeap (eraseE22 x) = mask bkHeap x := by
  unfold mask eraseE22
  simp (disch := decide) only [maskBank_set]

theorem npe_of_E20 {r r' : Regs} (h : E20Frame r r') : NonProjRegsEq bkHeap r r' := by
  unfold NonProjRegsEq
  rw [← mask_erase20 r', h, mask_erase20]

theorem npe_of_E22 {r r' : Regs} (h : E22Frame r r') : NonProjRegsEq bkHeap r r' := by
  unfold NonProjRegsEq
  rw [← mask_erase22 r', h, mask_erase22]

/-! Projections of `NonProjRegsEq bkHeap r r'`: every unmasked field, the masked view of each bank, and of PSTATE.
    These are the simp rules that move the B1 relation through the opaque step components (PMU/counter frames, action). -/
theorem fSP_EL3 {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : r'.SP_EL3 = r.SP_EL3 := congrArg (fun x => x.SP_EL3) h
theorem fSP_EL2 {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : r'.SP_EL2 = r.SP_EL2 := congrArg (fun x => x.SP_EL2) h
theorem fSP_EL1 {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : r'.SP_EL1 = r.SP_EL1 := congrArg (fun x => x.SP_EL1) h
theorem fmpam_vpmr_max {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : r'.__mpam_vpmr_max = r.__mpam_vpmr_max := congrArg (fun x => x.__mpam_vpmr_max) h
theorem fTSTATE {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : r'.TSTATE = r.TSTATE := congrArg (fun x => x.TSTATE) h
theorem fFPSR {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : r'.FPSR = r.FPSR := congrArg (fun x => x.FPSR) h
theorem fFPCR {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : r'.FPCR = r.FPCR := congrArg (fun x => x.FPCR) h
theorem fZT0 {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : r'._ZT0 = r._ZT0 := congrArg (fun x => x._ZT0) h
theorem fZA {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : r'._ZA = r._ZA := congrArg (fun x => x._ZA) h
theorem fFFR {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : r'._FFR = r._FFR := congrArg (fun x => x._FFR) h
theorem fP {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : r'._P = r._P := congrArg (fun x => x._P) h
theorem fZ {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : r'._Z = r._Z := congrArg (fun x => x._Z) h
theorem fRC {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : r'.RC = r.RC := congrArg (fun x => x.RC) h
theorem fVariantImplemented {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : r'.VariantImplemented = r.VariantImplemented := congrArg (fun x => x.VariantImplemented) h
theorem fFeatureImpl {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : r'.FeatureImpl = r.FeatureImpl := congrArg (fun x => x.FeatureImpl) h
theorem mb32 {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : maskBank bkHeap.b32 r'.bank_BitVec_32 = maskBank bkHeap.b32 r.bank_BitVec_32 :=
  congrArg (fun x => x.bank_BitVec_32) h
theorem mv32_16 {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : maskBank bkHeap.v32_16 r'.bank_Vector_BitVec_32_16 = maskBank bkHeap.v32_16 r.bank_Vector_BitVec_32_16 :=
  congrArg (fun x => x.bank_Vector_BitVec_32_16) h
theorem mv32_4 {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : maskBank bkHeap.v32_4 r'.bank_Vector_BitVec_32_4 = maskBank bkHeap.v32_4 r.bank_Vector_BitVec_32_4 :=
  congrArg (fun x => x.bank_Vector_BitVec_32_4) h
theorem mv64_32 {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : maskBank bkHeap.v64_32 r'.bank_Vector_BitVec_64_32 = maskBank bkHeap.v64_32 r.bank_Vector_BitVec_64_32 :=
  congrArg (fun x => x.bank_Vector_BitVec_64_32) h
theorem mb64 {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : maskBank bkHeap.b64 r'.bank_BitVec_64 = maskBank bkHeap.b64 r.bank_BitVec_64 :=
  congrArg (fun x => x.bank_BitVec_64) h
theorem mv64_16 {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : maskBank bkHeap.v64_16 r'.bank_Vector_BitVec_64_16 = maskBank bkHeap.v64_16 r.bank_Vector_BitVec_64_16 :=
  congrArg (fun x => x.bank_Vector_BitVec_64_16) h
theorem mv64_4 {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : maskBank bkHeap.v64_4 r'.bank_Vector_BitVec_64_4 = maskBank bkHeap.v64_4 r.bank_Vector_BitVec_64_4 :=
  congrArg (fun x => x.bank_Vector_BitVec_64_4) h
theorem mv32_31 {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : maskBank bkHeap.v32_31 r'.bank_Vector_BitVec_32_31 = maskBank bkHeap.v32_31 r.bank_Vector_BitVec_32_31 :=
  congrArg (fun x => x.bank_Vector_BitVec_32_31) h
theorem mbool {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : maskBank bkHeap.bool r'.bank_Bool = maskBank bkHeap.bool r.bank_Bool :=
  congrArg (fun x => x.bank_Bool) h
theorem mint {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : maskBank bkHeap.int r'.bank_Int = maskBank bkHeap.int r.bank_Int :=
  congrArg (fun x => x.bank_Int) h
theorem mb1 {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : maskBank bkHeap.b1 r'.bank_BitVec_1 = maskBank bkHeap.b1 r.bank_BitVec_1 :=
  congrArg (fun x => x.bank_BitVec_1) h
theorem mb56 {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : maskBank bkHeap.b56 r'.bank_BitVec_56 = maskBank bkHeap.b56 r.bank_BitVec_56 :=
  congrArg (fun x => x.bank_BitVec_56) h
theorem mb16 {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : maskBank bkHeap.b16 r'.bank_BitVec_16 = maskBank bkHeap.b16 r.bank_BitVec_16 :=
  congrArg (fun x => x.bank_BitVec_16) h
theorem mb4 {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : maskBank bkHeap.b4 r'.bank_BitVec_4 = maskBank bkHeap.b4 r.bank_BitVec_4 :=
  congrArg (fun x => x.bank_BitVec_4) h
theorem mb128 {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : maskBank bkHeap.b128 r'.bank_BitVec_128 = maskBank bkHeap.b128 r.bank_BitVec_128 :=
  congrArg (fun x => x.bank_BitVec_128) h
theorem mvbool32 {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : maskBank bkHeap.vbool32 r'.bank_Vector_Bool_32 = maskBank bkHeap.vbool32 r.bank_Vector_Bool_32 :=
  congrArg (fun x => x.bank_Vector_Bool_32) h
theorem mv64_64 {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : maskBank bkHeap.v64_64 r'.bank_Vector_BitVec_64_64 = maskBank bkHeap.v64_64 r.bank_Vector_BitVec_64_64 :=
  congrArg (fun x => x.bank_Vector_BitVec_64_64) h
theorem mirq {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : maskBank bkHeap.irq r'.bank_Option_InterruptID = maskBank bkHeap.irq r.bank_Option_InterruptID :=
  congrArg (fun x => x.bank_Option_InterruptID) h
theorem mb8 {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : maskBank bkHeap.b8 r'.bank_BitVec_8 = maskBank bkHeap.b8 r.bank_BitVec_8 :=
  congrArg (fun x => x.bank_BitVec_8) h
theorem mb2 {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : maskBank bkHeap.b2 r'.bank_BitVec_2 = maskBank bkHeap.b2 r.bank_BitVec_2 :=
  congrArg (fun x => x.bank_BitVec_2) h
theorem mv64_7 {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : maskBank bkHeap.v64_7 r'.bank_Vector_BitVec_64_7 = maskBank bkHeap.v64_7 r.bank_Vector_BitVec_64_7 :=
  congrArg (fun x => x.bank_Vector_BitVec_64_7) h
theorem msignal {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : maskBank bkHeap.signal r'.bank_Signal = maskBank bkHeap.signal r.bank_Signal :=
  congrArg (fun x => x.bank_Signal) h
theorem mps {r r' : Regs} (h : NonProjRegsEq bkHeap r r') : maskPSTATE r'.PSTATE = maskPSTATE r.PSTATE :=
  congrArg (fun x => x.PSTATE) h
/-- PSTATE updates of masked fields (the epilogue's BTYPE write, the NZCV of flag-setting actions) are invisible. -/
theorem mps_btype (ps : ProcState) (b : BitVec 2) : maskPSTATE { ps with BTYPE := b } = maskPSTATE ps := rfl
theorem mps_nzcv (ps : ProcState) (n z c v : BitVec 1) : maskPSTATE { ps with N := n, Z := z, C := c, V := v } = maskPSTATE ps := rfl

#print axioms npe_of_E20
#print axioms npe_of_E22
end ArmBridge.CruxNonProj
