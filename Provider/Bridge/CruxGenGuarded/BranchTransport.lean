import Bridge.CruxGenGuarded.BookkeepingTransport
import Bridge.CruxGenGuarded.InputCong
import Bridge.CruxGenBrDefs
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenBr
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! GENERATED from the selected native branch action frame and pin
schemas. Each class wrapper supplies its own fixed F-free action proof. -/

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.actbr_pins"
  (← IO.getStderr).flush

theorem actbr_pins (s t : NativeState) (hp : StepPins s) (hf : ActFrameBr s t) (hBTT : t.regs.Branchtypetaken ≠ BranchType.BranchType_RESET) : StepPins t := by
  have hPS_A := congrArg (fun p : ProcState => p.A) hf.pse
  change t.regs.PSTATE.A = s.regs.PSTATE.A at hPS_A
  have hPS_BTYPE := congrArg (fun p : ProcState => p.BTYPE) hf.pse
  change t.regs.PSTATE.BTYPE = s.regs.PSTATE.BTYPE at hPS_BTYPE
  have hPS_DIT := congrArg (fun p : ProcState => p.DIT) hf.pse
  change t.regs.PSTATE.DIT = s.regs.PSTATE.DIT at hPS_DIT
  have hPS_EL := congrArg (fun p : ProcState => p.EL) hf.pse
  change t.regs.PSTATE.EL = s.regs.PSTATE.EL at hPS_EL
  have hPS_F := congrArg (fun p : ProcState => p.F) hf.pse
  change t.regs.PSTATE.F = s.regs.PSTATE.F at hPS_F
  have hPS_I := congrArg (fun p : ProcState => p.I) hf.pse
  change t.regs.PSTATE.I = s.regs.PSTATE.I at hPS_I
  have hPS_IL := congrArg (fun p : ProcState => p.IL) hf.pse
  change t.regs.PSTATE.IL = s.regs.PSTATE.IL at hPS_IL
  have hPS_SS := congrArg (fun p : ProcState => p.SS) hf.pse
  change t.regs.PSTATE.SS = s.regs.PSTATE.SS at hPS_SS
  have hPS_nRW := congrArg (fun p : ProcState => p.nRW) hf.pse
  change t.regs.PSTATE.nRW = s.regs.PSTATE.nRW at hPS_nRW
  constructor
  · simpa (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128, hPS_A, hPS_BTYPE, hPS_DIT, hPS_EL, hPS_F, hPS_I, hPS_IL, hPS_SS, hPS_nRW] using hp.f4
  · simpa (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128, hPS_A, hPS_BTYPE, hPS_DIT, hPS_EL, hPS_F, hPS_I, hPS_IL, hPS_SS, hPS_nRW] using hp.rme
  · simpa (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128, hPS_A, hPS_BTYPE, hPS_DIT, hPS_EL, hPS_F, hPS_I, hPS_IL, hPS_SS, hPS_nRW] using hp.spe
  · simpa (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128, hPS_A, hPS_BTYPE, hPS_DIT, hPS_EL, hPS_F, hPS_I, hPS_IL, hPS_SS, hPS_nRW] using hp.el
  · simpa (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128, hPS_A, hPS_BTYPE, hPS_DIT, hPS_EL, hPS_F, hPS_I, hPS_IL, hPS_SS, hPS_nRW] using hp.nrw
  · simpa (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128, hPS_A, hPS_BTYPE, hPS_DIT, hPS_EL, hPS_F, hPS_I, hPS_IL, hPS_SS, hPS_nRW] using hp.edecr
  · simpa (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128, hPS_A, hPS_BTYPE, hPS_DIT, hPS_EL, hPS_F, hPS_I, hPS_IL, hPS_SS, hPS_nRW] using hp.cti
  · simpa (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128, hPS_A, hPS_BTYPE, hPS_DIT, hPS_EL, hPS_F, hPS_I, hPS_IL, hPS_SS, hPS_nRW] using hp.st
  · simpa (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128, hPS_A, hPS_BTYPE, hPS_DIT, hPS_EL, hPS_F, hPS_I, hPS_IL, hPS_SS, hPS_nRW] using hp.edesr
  · exact hBTT
  · simpa (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128, hPS_A, hPS_BTYPE, hPS_DIT, hPS_EL, hPS_F, hPS_I, hPS_IL, hPS_SS, hPS_nRW] using hp.emu
  · simpa (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128, hPS_A, hPS_BTYPE, hPS_DIT, hPS_EL, hPS_F, hPS_I, hPS_IL, hPS_SS, hPS_nRW] using hp.e2h
  · simpa (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128, hPS_A, hPS_BTYPE, hPS_DIT, hPS_EL, hPS_F, hPS_I, hPS_IL, hPS_SS, hPS_nRW] using hp.tge
  · simpa (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128, hPS_A, hPS_BTYPE, hPS_DIT, hPS_EL, hPS_F, hPS_I, hPS_IL, hPS_SS, hPS_nRW] using hp.scrns
  · simpa (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128, hPS_A, hPS_BTYPE, hPS_DIT, hPS_EL, hPS_F, hPS_I, hPS_IL, hPS_SS, hPS_nRW] using hp.pmbe
  · simpa (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128, hPS_A, hPS_BTYPE, hPS_DIT, hPS_EL, hPS_F, hPS_I, hPS_IL, hPS_SS, hPS_nRW] using hp.mdss
  · simpa (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128, hPS_A, hPS_BTYPE, hPS_DIT, hPS_EL, hPS_F, hPS_I, hPS_IL, hPS_SS, hPS_nRW] using hp.pmbs
  · simpa (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128, hPS_A, hPS_BTYPE, hPS_DIT, hPS_EL, hPS_F, hPS_I, hPS_IL, hPS_SS, hPS_nRW] using hp.da
  · simpa (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128, hPS_A, hPS_BTYPE, hPS_DIT, hPS_EL, hPS_F, hPS_I, hPS_IL, hPS_SS, hPS_nRW] using hp.di
  · simpa (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128, hPS_A, hPS_BTYPE, hPS_DIT, hPS_EL, hPS_F, hPS_I, hPS_IL, hPS_SS, hPS_nRW] using hp.df
  · simpa (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128, hPS_A, hPS_BTYPE, hPS_DIT, hPS_EL, hPS_F, hPS_I, hPS_IL, hPS_SS, hPS_nRW] using hp.il
  · simpa (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128, hPS_A, hPS_BTYPE, hPS_DIT, hPS_EL, hPS_F, hPS_I, hPS_IL, hPS_SS, hPS_nRW] using hp.pss
  · simpa (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128, hPS_A, hPS_BTYPE, hPS_DIT, hPS_EL, hPS_F, hPS_I, hPS_IL, hPS_SS, hPS_nRW] using hp.btype
  · simpa (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128, hPS_A, hPS_BTYPE, hPS_DIT, hPS_EL, hPS_F, hPS_I, hPS_IL, hPS_SS, hPS_nRW] using hp.btn


theorem actbr_sys (s t : NativeState) (hf : ActFrameBr s t) : SysEq2 s.regs t.regs := by
  have hPS_A := congrArg (fun p : ProcState => p.A) hf.pse
  change t.regs.PSTATE.A = s.regs.PSTATE.A at hPS_A
  have hPS_BTYPE := congrArg (fun p : ProcState => p.BTYPE) hf.pse
  change t.regs.PSTATE.BTYPE = s.regs.PSTATE.BTYPE at hPS_BTYPE
  have hPS_DIT := congrArg (fun p : ProcState => p.DIT) hf.pse
  change t.regs.PSTATE.DIT = s.regs.PSTATE.DIT at hPS_DIT
  have hPS_EL := congrArg (fun p : ProcState => p.EL) hf.pse
  change t.regs.PSTATE.EL = s.regs.PSTATE.EL at hPS_EL
  have hPS_F := congrArg (fun p : ProcState => p.F) hf.pse
  change t.regs.PSTATE.F = s.regs.PSTATE.F at hPS_F
  have hPS_I := congrArg (fun p : ProcState => p.I) hf.pse
  change t.regs.PSTATE.I = s.regs.PSTATE.I at hPS_I
  have hPS_IL := congrArg (fun p : ProcState => p.IL) hf.pse
  change t.regs.PSTATE.IL = s.regs.PSTATE.IL at hPS_IL
  have hPS_SS := congrArg (fun p : ProcState => p.SS) hf.pse
  change t.regs.PSTATE.SS = s.regs.PSTATE.SS at hPS_SS
  have hPS_nRW := congrArg (fun p : ProcState => p.nRW) hf.pse
  change t.regs.PSTATE.nRW = s.regs.PSTATE.nRW at hPS_nRW

  constructor <;> simp (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128, hPS_A, hPS_BTYPE, hPS_DIT, hPS_EL, hPS_F, hPS_I, hPS_IL, hPS_SS, hPS_nRW]

theorem actbr_branch (s t : NativeState) (hf : ActFrameBr s t) : BrSysEq s.regs t.regs := by
  constructor <;> simp (disch := decide) only [hf.bbool, hf.feat, hf.btn, hf.b64, hf.b32, hf.bint, hf.ss, hf.it, hf.enc, hf.emu, hf.b128]

theorem actbr_dit (s t : NativeState) (hf : ActFrameBr s t) : t.regs.PSTATE.DIT = s.regs.PSTATE.DIT := by
  have h := congrArg (fun p : ProcState => p.DIT) hf.pse
  exact h

#print axioms actbr_pins
#print axioms actbr_sys
#print axioms actbr_branch
#print axioms actbr_dit

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.preBr_of_spec"
  (← IO.getStderr).flush

set_option maxHeartbeats 200000 in
theorem preBr_of_spec (s sp : NativeState) (w : BitVec 32) (K : Int) (hp : StepPins s)
    (hE20 : E20Frame (clrGP (fetchRegs (preFetchRegs s.regs))) sp.regs)
    (hm : sp.mem = s.mem) : PreBr s (actionState w sp K) := by
  have hpf := fetch_pins s { s with regs := clrGP (fetchRegs (preFetchRegs s.regs)) } hp rfl
  have hps := e20_pins _ sp hpf hE20
  have hpt := metadata_pins w sp K hps
  have hf := PMUFrame.of_E20 hE20
  refine ⟨actionState_cong w s sp K (spec_input_cong s sp hE20 hm hp.el),
    ?_, ?_, hpt.btt, hpt.btn, ?_, hpt.st.trans hp.st.symm, hpt.edesr.trans hp.edesr.symm, ?_⟩
  · change sp.regs._PC = s.regs._PC
    exact hf.pc.trans (by rfl)
  · rfl
  · intro key hSEE hClock hLast
    have h := frame_pres_E20 (fun x : Regs => x.bank_Int key)
      (fun x => by simp (disch := first | assumption | decide) only [eraseE20, RegMap.set_ne]) hE20
    simpa (disch := first | assumption | decide) only [actionState, clrGP, fetchRegs,
      preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne] using h
  · intro key hC hI hS hO hB hM
    have h := frame_pres_E20 (fun x : Regs => x.bank_BitVec_64 key)
      (fun x => by simp (disch := first | assumption | decide) only [eraseE20, RegMap.set_ne]) hE20
    simpa (disch := first | assumption | decide) only [actionState, clrGP, fetchRegs,
      preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne] using h

#print axioms preBr_of_spec
end ArmBridge.CruxGenGuarded
