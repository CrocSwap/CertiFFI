import Bridge.CruxGenGuarded.FrameTransport
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! GENERATED pointwise transport for the actual native bookkeeping states.
All state functions are imported verbatim from the compiler-extracted pipeline.
No oracle independence or replacement of the actual full state is assumed. -/

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.fetch_pins"
  (← IO.getStderr).flush

theorem fetch_pins (s t : NativeState) (hp : StepPins s) (hr : t.regs = clrGP (fetchRegs (preFetchRegs s.regs))) : StepPins (t) := by
  constructor
  · simpa (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.f4] using hp.f4
  · simpa (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.rme] using hp.rme
  · simpa (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.spe] using hp.spe
  · simpa (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.el] using hp.el
  · simpa (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.nrw] using hp.nrw
  · simpa (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.edecr] using hp.edecr
  · simpa (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.cti] using hp.cti
  · simpa (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.st] using hp.st
  · simpa (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.edesr] using hp.edesr
  · simpa (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.btt] using hp.btt
  · simpa (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.emu] using hp.emu
  · simpa (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.e2h] using hp.e2h
  · simpa (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.tge] using hp.tge
  · simpa (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.scrns] using hp.scrns
  · simpa (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.pmbe] using hp.pmbe
  · simpa (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.mdss] using hp.mdss
  · simpa (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.pmbs] using hp.pmbs
  · simpa (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.da] using hp.da
  · simpa (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.di] using hp.di
  · simpa (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.df] using hp.df
  · simpa (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.il] using hp.il
  · simpa (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.pss] using hp.pss
  · simpa (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.btype] using hp.btype
  · simpa (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.btn] using hp.btn


run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.fetch_sys"
  (← IO.getStderr).flush

theorem fetch_sys (s t : NativeState) (hp : StepPins s) (hr : t.regs = clrGP (fetchRegs (preFetchRegs s.regs))) : SysEq2 s.regs (t).regs := by
  constructor
  all_goals first
    | rfl
    | assumption
    | simp (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.el, hp.nrw, hp.btn]

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.fetch_branch"
  (← IO.getStderr).flush

theorem fetch_branch (s t : NativeState) (hp : StepPins s) (hr : t.regs = clrGP (fetchRegs (preFetchRegs s.regs))) : BrSysEq s.regs (t).regs := by
  constructor
  all_goals first
    | rfl
    | assumption
    | simp (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.el, hp.nrw, hp.btn]

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.fetch_output"
  (← IO.getStderr).flush

theorem fetch_output (s t : NativeState) (hp : StepPins s) (hr : t.regs = clrGP (fetchRegs (preFetchRegs s.regs))) (hm : t.mem = s.mem) : CongOut (t) s := by
  constructor
  all_goals first
    | rfl
    | assumption
    | simp (disch := first | rfl | decide) only [hr, clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.el, hp.nrw, hp.btn]

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.metadata_pins"
  (← IO.getStderr).flush

theorem metadata_pins (w : BitVec 32) (s : NativeState) (K : Int) (hp : StepPins s)  : StepPins (actionState w s K) := by
  constructor
  · simpa (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.f4] using hp.f4
  · simpa (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.rme] using hp.rme
  · simpa (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.spe] using hp.spe
  · simpa (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.el] using hp.el
  · simpa (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.nrw] using hp.nrw
  · simpa (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.edecr] using hp.edecr
  · simpa (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.cti] using hp.cti
  · simpa (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.st] using hp.st
  · simpa (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.edesr] using hp.edesr
  · simpa (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.btt] using hp.btt
  · simpa (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.emu] using hp.emu
  · simpa (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.e2h] using hp.e2h
  · simpa (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.tge] using hp.tge
  · simpa (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.scrns] using hp.scrns
  · simpa (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.pmbe] using hp.pmbe
  · simpa (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.mdss] using hp.mdss
  · simpa (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.pmbs] using hp.pmbs
  · simpa (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.da] using hp.da
  · simpa (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.di] using hp.di
  · simpa (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.df] using hp.df
  · simpa (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.il] using hp.il
  · simpa (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.pss] using hp.pss
  · simpa (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.btype] using hp.btype
  · simpa (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.btn] using hp.btn


run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.metadata_sys"
  (← IO.getStderr).flush

theorem metadata_sys (w : BitVec 32) (s : NativeState) (K : Int) (hp : StepPins s)  : SysEq2 s.regs (actionState w s K).regs := by
  constructor
  all_goals first
    | rfl
    | assumption
    | simp (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.el, hp.nrw, hp.btn]

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.metadata_branch"
  (← IO.getStderr).flush

theorem metadata_branch (w : BitVec 32) (s : NativeState) (K : Int) (hp : StepPins s)  : BrSysEq s.regs (actionState w s K).regs := by
  constructor
  all_goals first
    | rfl
    | assumption
    | simp (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.el, hp.nrw, hp.btn]

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.metadata_output"
  (← IO.getStderr).flush

theorem metadata_output (w : BitVec 32) (s : NativeState) (K : Int) (hp : StepPins s)  : CongOut (actionState w s K) s := by
  constructor
  all_goals first
    | rfl
    | assumption
    | simp (disch := first | rfl | decide) only [actionState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.el, hp.nrw, hp.btn]

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.epilogue_not_taken_pins"
  (← IO.getStderr).flush

theorem epilogue_not_taken_pins (s : NativeState) (hp : StepPins s)  : StepPins (beforeCounterNotTaken s) := by
  constructor
  · simpa (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.f4] using hp.f4
  · simpa (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.rme] using hp.rme
  · simpa (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.spe] using hp.spe
  · simpa (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.el] using hp.el
  · simpa (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.nrw] using hp.nrw
  · simpa (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.edecr] using hp.edecr
  · simpa (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.cti] using hp.cti
  · simpa (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.st] using hp.st
  · simpa (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.edesr] using hp.edesr
  · simpa (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.btt] using hp.btt
  · simpa (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.emu] using hp.emu
  · simpa (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.e2h] using hp.e2h
  · simpa (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.tge] using hp.tge
  · simpa (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.scrns] using hp.scrns
  · simpa (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.pmbe] using hp.pmbe
  · simpa (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.mdss] using hp.mdss
  · simpa (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.pmbs] using hp.pmbs
  · simpa (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.da] using hp.da
  · simpa (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.di] using hp.di
  · simpa (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.df] using hp.df
  · simpa (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.il] using hp.il
  · simpa (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.pss] using hp.pss
  · simpa (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.btype] using hp.btype
  · simpa (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.btn] using hp.btn


run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.epilogue_not_taken_sys"
  (← IO.getStderr).flush

theorem epilogue_not_taken_sys (s : NativeState) (hp : StepPins s)  : SysEq2 s.regs (beforeCounterNotTaken s).regs := by
  constructor
  all_goals first
    | rfl
    | assumption
    | simp (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.el, hp.nrw, hp.btn]

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.epilogue_not_taken_branch"
  (← IO.getStderr).flush

theorem epilogue_not_taken_branch (s : NativeState) (hp : StepPins s)  : BrSysEq s.regs (beforeCounterNotTaken s).regs := by
  constructor
  all_goals first
    | rfl
    | assumption
    | simp (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.el, hp.nrw, hp.btn]

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.epilogue_not_taken_output"
  (← IO.getStderr).flush

theorem epilogue_not_taken_output (s : NativeState) (hp : StepPins s)  : CongOut (beforeCounterNotTaken s) s := by
  constructor
  all_goals first
    | rfl
    | assumption
    | simp (disch := first | rfl | decide) only [beforeCounterNotTaken, beforeCounterNotTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.el, hp.nrw, hp.btn]

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.epilogue_taken_pins"
  (← IO.getStderr).flush

theorem epilogue_taken_pins (s : NativeState) (hp : StepPins s)  : StepPins (beforeCounterTaken s) := by
  constructor
  · simpa (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.f4] using hp.f4
  · simpa (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.rme] using hp.rme
  · simpa (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.spe] using hp.spe
  · simpa (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.el] using hp.el
  · simpa (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.nrw] using hp.nrw
  · simpa (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.edecr] using hp.edecr
  · simpa (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.cti] using hp.cti
  · simpa (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.st] using hp.st
  · simpa (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.edesr] using hp.edesr
  · simpa (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.btt] using hp.btt
  · simpa (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.emu] using hp.emu
  · simpa (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.e2h] using hp.e2h
  · simpa (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.tge] using hp.tge
  · simpa (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.scrns] using hp.scrns
  · simpa (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.pmbe] using hp.pmbe
  · simpa (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.mdss] using hp.mdss
  · simpa (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.pmbs] using hp.pmbs
  · simpa (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.da] using hp.da
  · simpa (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.di] using hp.di
  · simpa (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.df] using hp.df
  · simpa (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.il] using hp.il
  · simpa (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.pss] using hp.pss
  · simpa (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.btype] using hp.btype
  · simpa (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.btn] using hp.btn


run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.epilogue_taken_sys"
  (← IO.getStderr).flush

theorem epilogue_taken_sys (s : NativeState) (hp : StepPins s)  : SysEq2 s.regs (beforeCounterTaken s).regs := by
  constructor
  all_goals first
    | rfl
    | assumption
    | simp (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.el, hp.nrw, hp.btn]

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.epilogue_taken_branch"
  (← IO.getStderr).flush

theorem epilogue_taken_branch (s : NativeState) (hp : StepPins s)  : BrSysEq s.regs (beforeCounterTaken s).regs := by
  constructor
  all_goals first
    | rfl
    | assumption
    | simp (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.el, hp.nrw, hp.btn]

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.epilogue_taken_output"
  (← IO.getStderr).flush

theorem epilogue_taken_output (s : NativeState) (hp : StepPins s)  : CongOut (beforeCounterTaken s) s := by
  constructor
  all_goals first
    | rfl
    | assumption
    | simp (disch := first | rfl | decide) only [beforeCounterTaken, beforeCounterTakenWithNext, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.el, hp.nrw, hp.btn]

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.end_cycle_pins"
  (← IO.getStderr).flush

theorem end_cycle_pins (s : NativeState) (hp : StepPins s)  : StepPins (nativeEndState s) := by
  constructor
  · simpa (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.f4] using hp.f4
  · simpa (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.rme] using hp.rme
  · simpa (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.spe] using hp.spe
  · simpa (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.el] using hp.el
  · simpa (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.nrw] using hp.nrw
  · simpa (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.edecr] using hp.edecr
  · simpa (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.cti] using hp.cti
  · simpa (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.st] using hp.st
  · simpa (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.edesr] using hp.edesr
  · simpa (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.btt] using hp.btt
  · simpa (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.emu] using hp.emu
  · simpa (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.e2h] using hp.e2h
  · simpa (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.tge] using hp.tge
  · simpa (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.scrns] using hp.scrns
  · simpa (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.pmbe] using hp.pmbe
  · simpa (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.mdss] using hp.mdss
  · simpa (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.pmbs] using hp.pmbs
  · simpa (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.da] using hp.da
  · simpa (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.di] using hp.di
  · simpa (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.df] using hp.df
  · simpa (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.il] using hp.il
  · simpa (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.pss] using hp.pss
  · simpa (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.btype] using hp.btype
  · simpa (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.btn] using hp.btn


run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.end_cycle_sys"
  (← IO.getStderr).flush

theorem end_cycle_sys (s : NativeState) (hp : StepPins s)  : SysEq2 s.regs (nativeEndState s).regs := by
  constructor
  all_goals first
    | rfl
    | assumption
    | simp (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.el, hp.nrw, hp.btn]

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.end_cycle_branch"
  (← IO.getStderr).flush

theorem end_cycle_branch (s : NativeState) (hp : StepPins s)  : BrSysEq s.regs (nativeEndState s).regs := by
  constructor
  all_goals first
    | rfl
    | assumption
    | simp (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.el, hp.nrw, hp.btn]

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.end_cycle_output"
  (← IO.getStderr).flush

theorem end_cycle_output (s : NativeState) (hp : StepPins s)  : CongOut (nativeEndState s) s := by
  constructor
  all_goals first
    | rfl
    | assumption
    | simp (disch := first | rfl | decide) only [nativeEndState, Register.__InstructionStep, Register.BTypeCompatible, Register.BTypeNext, Register.__cycle_count, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int, RegMap.set_ne, RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv, hde_pipeadv, hp.el, hp.nrw, hp.btn]

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.fetch_nonProj"
  (← IO.getStderr).flush

theorem fetch_nonProj (s t : NativeState)
    (hr : t.regs = clrGP (fetchRegs (preFetchRegs s.regs))) :
    ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap s.regs t.regs := by
  rw [hr]
  simp (disch := decide) only [ArmCertCT.CT2.NonProjRegsEq, ArmCertCT.CT2.mask,
    clrGP, fetchRegs, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible,
    Regs.ref_Bool, ArmBridge.CruxNonProj.maskBank_set]

#print axioms fetch_pins
#print axioms fetch_sys
#print axioms fetch_branch
#print axioms fetch_output
#print axioms metadata_pins
#print axioms metadata_sys
#print axioms metadata_branch
#print axioms metadata_output
#print axioms epilogue_not_taken_pins
#print axioms epilogue_not_taken_sys
#print axioms epilogue_not_taken_branch
#print axioms epilogue_not_taken_output
#print axioms epilogue_taken_pins
#print axioms epilogue_taken_sys
#print axioms epilogue_taken_branch
#print axioms epilogue_taken_output
#print axioms end_cycle_pins
#print axioms end_cycle_sys
#print axioms end_cycle_branch
#print axioms end_cycle_output
#print axioms fetch_nonProj
end ArmBridge.CruxGenGuarded
