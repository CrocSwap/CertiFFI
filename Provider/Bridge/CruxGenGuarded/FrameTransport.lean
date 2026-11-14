import Bridge.CruxGenGuarded.Cycle
import Bridge.CruxGen
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! GENERATED from the selected native StepPins/SysEq2/BrSysEq/CongOut
schemas. Frame premises concern ONE actual successor; they are internal
owner-filled facts, not public caller execution/frame admission answers. -/

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.e20_sys"
  (← IO.getStderr).flush

theorem e20_sys (r r' : Regs) (hE : E20Frame r r') : SysEq2 r r' := by
  constructor
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.FeatureImpl)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.EL)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.nRW)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.bank_BitVec_64 .SCTLR_EL2)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.bank_BitVec_64 .TCR_EL2)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.bank_BitVec_64 .TCR2_EL2)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.bank_BitVec_64 .HCR_EL2)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.bank_BitVec_64 .SCR_EL3)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.bank_BitVec_64 .MAIR_EL2)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.bank_BitVec_64 .MDSCR_EL1)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.bank_BitVec_64 .HTTBR)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.bank_BitVec_128 ._TTBR0_EL2)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.bank_BitVec_128 .TTBR1_EL2)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => _get_EDSCR_Type_HDE (x.bank_BitVec_32 ._EDSCR))
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.bank_Bool .__tlb_enabled)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.bank_Bool .SPESampleInFlight)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.bank_Int .__supported_pa_size)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf


run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.e20_branch"
  (← IO.getStderr).flush

theorem e20_branch (r r' : Regs) (hE : E20Frame r r') : BrSysEq r r' := by
  constructor
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.bank_Int .NUM_BREAKPOINTS)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.bank_Int .NUM_WATCHPOINTS)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.bank_Int .__num_ctx_breakpoints)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.bank_BitVec_64 .MDCR_EL3)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf


run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.e20_pins"
  (← IO.getStderr).flush

theorem e20_pins (s t : NativeState) (hp : StepPins s) (hE : E20Frame s.regs t.regs) : StepPins t := by
  constructor
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.FeatureImpl[4]! = true)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf.mpr hp.f4
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.FeatureImpl[232]! = false)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf.mpr hp.rme
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.bank_Bool .SPESampleInFlight = false)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf.mpr hp.spe
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.EL = 0#2)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf.mpr hp.el
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.nRW = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf.mpr hp.nrw
  ·
    have hf := frame_pres_E20 (fun x : Regs => _get_EDECR_Type_RCE (x.bank_BitVec_32 .EDECR) = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf.mpr hp.edecr
  ·
    have hf := frame_pres_E20 (fun x : Regs => _get_CTIDEVCTL_Type_RCE (x.bank_BitVec_32 .CTIDEVCTL) = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf.mpr hp.cti
  ·
    have hf := frame_pres_E20 (fun x : Regs => _get_EDSCR_Type_STATUS (x.bank_BitVec_32 ._EDSCR) = 0b000010#6)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf.mpr hp.st
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.bank_BitVec_32 .EDESR = 0#32)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf.mpr hp.edesr
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.Branchtypetaken ≠ BranchType.BranchType_RESET)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf.mpr hp.btt
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.__emulator_termination_opcode = none)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf.mpr hp.emu
  ·
    have hf := frame_pres_E20 (fun x : Regs => _get_HCR_EL2_Type_E2H (x.bank_BitVec_64 .HCR_EL2) = 1#1)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf.mpr hp.e2h
  ·
    have hf := frame_pres_E20 (fun x : Regs => _get_HCR_EL2_Type_TGE (x.bank_BitVec_64 .HCR_EL2) = 1#1)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf.mpr hp.tge
  ·
    have hf := frame_pres_E20 (fun x : Regs => _get_SCR_EL3_Type_NS (x.bank_BitVec_64 .SCR_EL3) = 1#1)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf.mpr hp.scrns
  ·
    have hf := frame_pres_E20 (fun x : Regs => _get_PMBLIMITR_EL1_Type_E (x.bank_BitVec_64 .PMBLIMITR_EL1) = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf.mpr hp.pmbe
  ·
    have hf := frame_pres_E20 (fun x : Regs => _get_MDSCR_EL1_Type_SS (x.bank_BitVec_64 .MDSCR_EL1) = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf.mpr hp.mdss
  ·
    have hf := frame_pres_E20 (fun x : Regs => Sail.BitVec.extractLsb (x.bank_BitVec_64 .PMBSR_EL1) 17 17 = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf.mpr hp.pmbs
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.A = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf.mpr hp.da
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.I = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf.mpr hp.di
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.F = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf.mpr hp.df
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.IL = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf.mpr hp.il
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.SS = 0#1)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf.mpr hp.pss
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.BTYPE = 0#2)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf.mpr hp.btype
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.BTypeNext = 0#2)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf.mpr hp.btn


run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.e20_output"
  (← IO.getStderr).flush

theorem e20_output (s t : NativeState) (hE : E20Frame s.regs t.regs) (hm : t.mem = s.mem) : CongOut t s := by
  constructor
  · exact hm
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.gpr)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.SP_EL0)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => x._Z)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.N)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.Z)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.C)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E20 (fun x : Regs => x.PSTATE.V)
      (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) hE
    exact hf


run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.e22_sys"
  (← IO.getStderr).flush

theorem e22_sys (r r' : Regs) (hE : E22Frame r r') : SysEq2 r r' := by
  constructor
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.FeatureImpl)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.PSTATE.EL)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.PSTATE.nRW)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.bank_BitVec_64 .SCTLR_EL2)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.bank_BitVec_64 .TCR_EL2)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.bank_BitVec_64 .TCR2_EL2)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.bank_BitVec_64 .HCR_EL2)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.bank_BitVec_64 .SCR_EL3)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.bank_BitVec_64 .MAIR_EL2)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.bank_BitVec_64 .MDSCR_EL1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.bank_BitVec_64 .HTTBR)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.bank_BitVec_128 ._TTBR0_EL2)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.bank_BitVec_128 .TTBR1_EL2)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => _get_EDSCR_Type_HDE (x.bank_BitVec_32 ._EDSCR))
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.bank_Bool .__tlb_enabled)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.bank_Bool .SPESampleInFlight)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.bank_Int .__supported_pa_size)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf


run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.e22_branch"
  (← IO.getStderr).flush

theorem e22_branch (r r' : Regs) (hE : E22Frame r r') : BrSysEq r r' := by
  constructor
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.bank_Int .NUM_BREAKPOINTS)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.bank_Int .NUM_WATCHPOINTS)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.bank_Int .__num_ctx_breakpoints)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.bank_BitVec_64 .MDCR_EL3)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf


run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.e22_pins"
  (← IO.getStderr).flush

theorem e22_pins (s t : NativeState) (hp : StepPins s) (hE : E22Frame s.regs t.regs) : StepPins t := by
  constructor
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.FeatureImpl[4]! = true)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.f4
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.FeatureImpl[232]! = false)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.rme
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.bank_Bool .SPESampleInFlight = false)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.spe
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.PSTATE.EL = 0#2)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.el
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.PSTATE.nRW = 0#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.nrw
  ·
    have hf := frame_pres_E22 (fun x : Regs => _get_EDECR_Type_RCE (x.bank_BitVec_32 .EDECR) = 0#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.edecr
  ·
    have hf := frame_pres_E22 (fun x : Regs => _get_CTIDEVCTL_Type_RCE (x.bank_BitVec_32 .CTIDEVCTL) = 0#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.cti
  ·
    have hf := frame_pres_E22 (fun x : Regs => _get_EDSCR_Type_STATUS (x.bank_BitVec_32 ._EDSCR) = 0b000010#6)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.st
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.bank_BitVec_32 .EDESR = 0#32)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.edesr
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.Branchtypetaken ≠ BranchType.BranchType_RESET)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.btt
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.__emulator_termination_opcode = none)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.emu
  ·
    have hf := frame_pres_E22 (fun x : Regs => _get_HCR_EL2_Type_E2H (x.bank_BitVec_64 .HCR_EL2) = 1#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.e2h
  ·
    have hf := frame_pres_E22 (fun x : Regs => _get_HCR_EL2_Type_TGE (x.bank_BitVec_64 .HCR_EL2) = 1#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.tge
  ·
    have hf := frame_pres_E22 (fun x : Regs => _get_SCR_EL3_Type_NS (x.bank_BitVec_64 .SCR_EL3) = 1#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.scrns
  ·
    have hf := frame_pres_E22 (fun x : Regs => _get_PMBLIMITR_EL1_Type_E (x.bank_BitVec_64 .PMBLIMITR_EL1) = 0#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.pmbe
  ·
    have hf := frame_pres_E22 (fun x : Regs => _get_MDSCR_EL1_Type_SS (x.bank_BitVec_64 .MDSCR_EL1) = 0#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.mdss
  ·
    have hf := frame_pres_E22 (fun x : Regs => Sail.BitVec.extractLsb (x.bank_BitVec_64 .PMBSR_EL1) 17 17 = 0#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.pmbs
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.PSTATE.A = 0#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.da
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.PSTATE.I = 0#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.di
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.PSTATE.F = 0#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.df
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.PSTATE.IL = 0#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.il
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.PSTATE.SS = 0#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.pss
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.PSTATE.BTYPE = 0#2)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.btype
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.BTypeNext = 0#2)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.btn


run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.e22_output"
  (← IO.getStderr).flush

theorem e22_output (s t : NativeState) (hE : E22Frame s.regs t.regs) (hm : t.mem = s.mem) : CongOut t s := by
  constructor
  · exact hm
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.gpr)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.SP_EL0)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => x._Z)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.PSTATE.N)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.PSTATE.Z)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.PSTATE.C)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf
  ·
    have hf := frame_pres_E22 (fun x : Regs => x.PSTATE.V)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf


run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.congOut_trans"
  (← IO.getStderr).flush

theorem congOut_trans (a b c : NativeState) (hab : CongOut a b) (hbc : CongOut b c) : CongOut a c := by
  exact ⟨hab.mem.trans hbc.mem, hab.gpr.trans hbc.gpr, hab.sp.trans hbc.sp, hab.z.trans hbc.z, hab.n.trans hbc.n, hab.zf.trans hbc.zf, hab.c.trans hbc.c, hab.v.trans hbc.v⟩


run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.sysEq2_trans"
  (← IO.getStderr).flush

theorem sysEq2_trans (a b c : Regs) (hab : SysEq2 a b) (hbc : SysEq2 b c) : SysEq2 a c := by
  exact ⟨hbc.feat.trans hab.feat, hbc.el.trans hab.el, hbc.nrw.trans hab.nrw, hbc.sctlr.trans hab.sctlr, hbc.tcr.trans hab.tcr, hbc.tcr2.trans hab.tcr2, hbc.hcr.trans hab.hcr, hbc.scr.trans hab.scr, hbc.mair.trans hab.mair, hbc.mdscr.trans hab.mdscr, hbc.httbr.trans hab.httbr, hbc.ttbr0.trans hab.ttbr0, hbc.ttbr1.trans hab.ttbr1, hbc.hde.trans hab.hde, hbc.tlb.trans hab.tlb, hbc.spe.trans hab.spe, hbc.pa.trans hab.pa⟩


run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.brSysEq_trans"
  (← IO.getStderr).flush

theorem brSysEq_trans (a b c : Regs) (hab : BrSysEq a b) (hbc : BrSysEq b c) : BrSysEq a c := by
  exact ⟨hbc.nbp.trans hab.nbp, hbc.nwp.trans hab.nwp, hbc.nctx.trans hab.nctx, hbc.mdcr3.trans hab.mdcr3⟩


#print axioms e20_sys
#print axioms e20_branch
#print axioms e20_pins
#print axioms e20_output
#print axioms e22_sys
#print axioms e22_branch
#print axioms e22_pins
#print axioms e22_output
#print axioms congOut_trans
#print axioms sysEq2_trans
#print axioms brSysEq_trans
end ArmBridge.CruxGenGuarded
