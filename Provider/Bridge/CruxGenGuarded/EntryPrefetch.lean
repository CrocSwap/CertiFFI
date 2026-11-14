import Bridge.CruxGenGuarded.Prefetch
import NativeEntryTail.Guard
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/- Internal composition at the actual fetch call, using the unchanged
canonical prefix/tail functions. No fetch success, current-state frame or
future quietness is supplied at public Entry. The real fetch producer must
derive fetchRun and the primitive fetched emulator control below. No incoming
BTYPE/BTN, readonly-memory or synthetic clrGP/fetchRegs result is assumed. -/
run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.entry_prefetch_boundary"
  (← IO.getStderr).flush

theorem entry_prefetch_boundary (real : Type) [Sail.SailReal real]
    (s fetched : NativeState) (w : BitVec 32) (pins : NativeEntryTail.EntryPins s)
    (hGIC : s.regs.bank_Option_InterruptID .__GIC_Pending = none)
    (fetchRun : (__FetchInstr s.regs._PC : SailM (__InstrEnc × BitVec 32))
      (beforeFetchState s) = .ok (.__A64, w) fetched)
    (emu : fetched.regs.__emulator_termination_opcode = none) :
    ∃ enc0, modelStep real s = nativeTail real s w enc0 fetched := by
  obtain ⟨enc0, henc⟩ := uenc (ChoiceLabel.site 7637) (encodingState s)
  dsimp only [encodingState] at henc
  refine ⟨enc0, ?_⟩
  unfold modelStep __TopLevel
  simp only [ArmBridge.Awc.ite_cond]
  simp only [bind, EStateM.bind, Sail.ConcurrencyInterfaceV1.PreSail.readReg_apply,
    Sail.ConcurrencyInterfaceV1.PreSail.writeReg_apply, ArmBridge.BKmin.Halted, ubool]
  simp only [BK3_Halted.native]
  simp (config := {decide := true}) only [bind, EStateM.bind, Sail.ConcurrencyInterfaceV1.PreSail.readReg_apply, pins.st,
    ArmFull.Register.SEE, ArmFull.Register._EDSCR, ite_true, ite_false, Bool.false_eq_true, reduceIte, Bool.not_false, Bool.not_true]
  have hST' : Sail.BitVec.extractLsb (s.regs.bank_BitVec_32 ._EDSCR) 5 0 = 2#6 := by
    simpa [_get_EDSCR_Type_STATUS] using pins.st
  simp (config := {decide := true}) only [Regs.ref_Int, hST', reduceIte, ite_true, ite_false, Bool.false_eq_true,
    Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, decide_false, decide_true,
    BitVec.reduceBEq, BitVec.reduceEq, beq_self_eq_true, Bool.not_true, Bool.cond_false, Bool.cond_true]
  simp only [undefined_InterruptReq, bind, EStateM.bind, ubool, pure, EStateM.pure]
  rw [tc_apply]
  simp only [EStateM.bind]
  rw [tpi_frame]
  rotate_left
  all_goals first
    | (simp only [SEE, Regs.ref_Int, pins.f4, pins.el, pins.nrw, pins.e2h, pins.tge, hGIC, pins.da, pins.di, pins.df]; done)
    | skip
  simp only [Sail.ConcurrencyInterfaceV1.PreSail.readReg_apply, Bool.not_false, ite_true, EStateM.bind, Bool.cond_true, Bool.cond_false, Bool.not_false]
  simp only [Branchtypetaken, Regs.ref_Int]
  have hBT' : (s.regs.Branchtypetaken == BranchType.BranchType_RESET) = false := by
    have hBT := pins.btt
    revert hBT; cases s.regs.Branchtypetaken <;> intro h1 <;> first | exact absurd rfl h1 | rfl
  simp only [hBT', Bool.cond_false]
  unfold __InstructionExecute
  simp only [ArmBridge.Awc.ite_cond]
  simp only [↓bind_app]
  erw [henc]
  simp only [ubv, ArmBridge.BKmin.EDSCRread, BK3_EDSCRread.native, ArmBridge.BKmin.EDSCRwritePipeAdv,
    BK3_EDSCRwritePipeAdv.native, Sail.ConcurrencyInterfaceV1.PreSail.readReg_apply]
  have hZ : IsZero (0#32) = true := by decide
  simp only [EDESR, Regs.ref_BitVec_32, ArmFull.Register._EDSCR, ArmFull.Register.MDCCSR_EL0, Regs.ref_BitVec_64]
  simp (disch := decide) only [Sail.ConcurrencyInterfaceV1.RegMap.set_ne, Sail.ConcurrencyInterfaceV1.RegMap.set_same,
    pins.edesr, hZ, Bool.not_true, Bool.cond_false]
  simp only [↓bind_app]
  rw [tc_apply]
  simp only [↓bind_app, Sail.ConcurrencyInterfaceV1.PreSail.readReg_apply, Sail.ConcurrencyInterfaceV1.PreSail.writeReg_apply,
    pure, EStateM.pure, PSTATE, ShouldAdvanceIT, ShouldAdvanceSS, pins.nrw, ArmBridge.BKmin.ThisInstrAddr64, BK3_ThisInstrAddr64.native]
  simp (config := {decide := true}) only [pins.nrw, BitVec.reduceBEq, Bool.cond_false, Bool.cond_true, beq_self_eq_true,
    ↓bind_app, EStateM.pure, pure, Sail.ConcurrencyInterfaceV1.PreSail.readReg_apply,
    Sail.ConcurrencyInterfaceV1.PreSail.writeReg_apply]
  rw [pc_id]
  erw [fetchRun]
  simp only []
  rw [ArmBridge.BKmin.emu (real := real) _ _ _ emu]
  simp only [ArmBridge.BKv.emu_native]
  unfold nativeTail
  dsimp only [beforeFetchState]

#print axioms entry_prefetch_boundary
end ArmBridge.CruxGenGuarded
