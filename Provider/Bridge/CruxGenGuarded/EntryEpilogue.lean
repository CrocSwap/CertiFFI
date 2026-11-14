import Bridge.CruxGenGuarded.UniformEpilogue
import NativeEntryTail.Guard
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
open NativeEntryTail (EntryPins)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

run_cmd do
  IO.eprintln "CURRENT_DECL EntryEpilogue.epilogue_current_NotTaken"
  (← IO.getStderr).flush

theorem epilogue_current_NotTaken (real : Type) [Sail.SailReal real] (s : NativeState) (hp : EntryPins s)
      (hEnc : s.regs.__ThisInstrEnc = .__A64)
      (hEret : (Sail.BitVec.extractLsb (s.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false)
      (hIT : s.regs.ShouldAdvanceIT = false) (hSS : s.regs.ShouldAdvanceSS = true)
      (hTaken : s.regs.__BranchTaken = false )
       :
    nativeAfterRetired s = nativeAtCounter (beforeCounterNotTakenWithNext s.regs.BTypeNext s) := by
  have hF4' : s.regs.FeatureImpl[4] = true := by simpa using hp.f4
  have hRME' : s.regs.FeatureImpl[232] = false := by simpa using hp.rme
  unfold ArmBridge.CruxGenGuarded.nativeAfterRetired
  rw [ArmBridge.BKmin.spePost real]
  rotate_left
  · simp (disch := first | rfl | decide) [fetchRegs, clrGP, preFetchRegs, hp.spe, Sail.ConcurrencyInterfaceV1.RegMap.set_ne, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  simp only [ArmBridge.BKv.spePost_native, ↓bind_app, Sail.ConcurrencyInterfaceV1.PreSail.writeReg_apply, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  rw [ArmBridge.BKmin.eret, ArmBridge.BK.eret_native]
  simp (disch := first | rfl | decide) only [InGuardedPage, Regs.ref_Bool, Regs.ref_BitVec_32, __currentCond, __ThisInstr, Regs.ref_BitVec_4, Sail.ConcurrencyInterfaceV1.RegMap.set_ne, Sail.ConcurrencyInterfaceV1.RegMap.set_same, hEret, Bool.not_false, Bool.cond_true, ite_true, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  simp only [↓bind_app, Sail.ConcurrencyInterfaceV1.PreSail.readReg_apply, Sail.ConcurrencyInterfaceV1.PreSail.writeReg_apply, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  simp (disch := first | rfl | decide) only [__BranchTaken, ShouldAdvanceIT, ShouldAdvanceSS, PSTATE, InGuardedPage, Regs.ref_Bool, Sail.ConcurrencyInterfaceV1.RegMap.set_ne, Bool.not_false, Bool.cond_true, Bool.cond_false, ite_true, ite_false, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  simp only [↓bind_app, Sail.ConcurrencyInterfaceV1.PreSail.readReg_apply, Sail.ConcurrencyInterfaceV1.PreSail.writeReg_apply, ArmBridge.BKmin.ThisInstrLength, BK3_ThisInstrLength.native, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  simp (disch := first | rfl | decide) only [__ThisInstrEnc, InGuardedPage, Regs.ref_Bool, __currentCond, __ThisInstr, Regs.ref_BitVec_4, Regs.ref_BitVec_32, ShouldAdvanceIT, ShouldAdvanceSS, PSTATE, _PC, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  simp (config := {decide := true}) only [beq_self_eq_true, Bool.cond_true, Bool.cond_false, ite_true, ite_false, reduceIte, Bool.false_eq_true, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  simp only [↓bind_app, Sail.ConcurrencyInterfaceV1.PreSail.readReg_apply, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  simp (disch := first | rfl | decide) only [Bool.cond_true, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  rw [ssadv_frame]
  rotate_left
  all_goals first
    | (simp (disch := first | rfl | assumption | decide) [Sail.ConcurrencyInterfaceV1.RegMap.set_ne, fetchRegs, clrGP, preFetchRegs, hp.f4, hp.rme, hF4', hRME', hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]; done)
    | skip
  unfold __CycleEnd
  simp only [ArmBridge.Awc.ite_cond, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  simp only [↓bind_app, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  rw [speCycle_frame real]
  rotate_left
  · simp (disch := first | rfl | decide) only [hp.spe, InGuardedPage, Regs.ref_Bool, Regs.ref_BitVec_32, Regs.ref_BitVec_64, Regs.ref_Int, Regs.ref_BitVec_4, __currentCond, __ThisInstr, __ThisInstrEnc, __ExclusiveMonitorSet, __BranchTaken, SEE, PSTATE, _PC, fetchRegs, clrGP, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Sail.ConcurrencyInterfaceV1.RegMap.set_ne, Sail.ConcurrencyInterfaceV1.RegMap.set_same, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  · simp (disch := first | rfl | decide) only [hp.pmbs, InGuardedPage, Regs.ref_Bool, Regs.ref_BitVec_32, Regs.ref_BitVec_64, Regs.ref_Int, Regs.ref_BitVec_4, __currentCond, __ThisInstr, __ThisInstrEnc, __ExclusiveMonitorSet, __BranchTaken, SEE, PSTATE, _PC, fetchRegs, clrGP, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Sail.ConcurrencyInterfaceV1.RegMap.set_ne, Sail.ConcurrencyInterfaceV1.RegMap.set_same, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  simp only [↓bind_app, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  unfold nativeAtCounter beforeCounterNotTakenWithNext
  dsimp only []


run_cmd do
  IO.eprintln "CURRENT_DECL EntryEpilogue.epilogue_current_Taken"
  (← IO.getStderr).flush

theorem epilogue_current_Taken (real : Type) [Sail.SailReal real] (s : NativeState) (hp : EntryPins s)
      (hEnc : s.regs.__ThisInstrEnc = .__A64)
      (hEret : (Sail.BitVec.extractLsb (s.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false)
      (hIT : s.regs.ShouldAdvanceIT = false) (hSS : s.regs.ShouldAdvanceSS = true)
      (hTaken : s.regs.__BranchTaken = true )
       :
    nativeAfterRetired s = nativeAtCounter (beforeCounterTakenWithNext s.regs.BTypeNext s) := by
  have hF4' : s.regs.FeatureImpl[4] = true := by simpa using hp.f4
  have hRME' : s.regs.FeatureImpl[232] = false := by simpa using hp.rme
  unfold ArmBridge.CruxGenGuarded.nativeAfterRetired
  rw [ArmBridge.BKmin.spePost real]
  rotate_left
  · simp (disch := first | rfl | decide) [fetchRegs, clrGP, preFetchRegs, hp.spe, Sail.ConcurrencyInterfaceV1.RegMap.set_ne, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  try simp only [ArmBridge.BKv.spePost_native, ↓bind_app, Sail.ConcurrencyInterfaceV1.PreSail.writeReg_apply, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  rw [ArmBridge.BKmin.eret, ArmBridge.BK.eret_native]
  try simp (disch := first | rfl | decide) only [InGuardedPage, Regs.ref_Bool, Regs.ref_BitVec_32, __currentCond, __ThisInstr, Regs.ref_BitVec_4, Sail.ConcurrencyInterfaceV1.RegMap.set_ne, Sail.ConcurrencyInterfaceV1.RegMap.set_same, hEret, Bool.not_false, Bool.cond_true, ite_true, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  try simp only [↓bind_app, Sail.ConcurrencyInterfaceV1.PreSail.readReg_apply, Sail.ConcurrencyInterfaceV1.PreSail.writeReg_apply, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  try simp (disch := first | rfl | decide) only [__BranchTaken, ShouldAdvanceIT, ShouldAdvanceSS, PSTATE, InGuardedPage, Regs.ref_Bool, Sail.ConcurrencyInterfaceV1.RegMap.set_ne, Bool.not_false, Bool.cond_true, Bool.cond_false, ite_true, ite_false, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  try simp only [↓bind_app, Sail.ConcurrencyInterfaceV1.PreSail.readReg_apply, Sail.ConcurrencyInterfaceV1.PreSail.writeReg_apply, ArmBridge.BKmin.ThisInstrLength, BK3_ThisInstrLength.native, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  try simp (disch := first | rfl | decide) only [__ThisInstrEnc, InGuardedPage, Regs.ref_Bool, __currentCond, __ThisInstr, Regs.ref_BitVec_4, Regs.ref_BitVec_32, ShouldAdvanceIT, ShouldAdvanceSS, PSTATE, _PC, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  try simp (config := {decide := true}) only [beq_self_eq_true, Bool.cond_true, Bool.cond_false, ite_true, ite_false, reduceIte, Bool.false_eq_true, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  try simp only [↓bind_app, Sail.ConcurrencyInterfaceV1.PreSail.readReg_apply, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  try simp (disch := first | rfl | decide) only [Bool.cond_true, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  rw [ssadv_frame]
  rotate_left
  all_goals first
    | (simp (disch := first | rfl | assumption | decide) [Sail.ConcurrencyInterfaceV1.RegMap.set_ne, fetchRegs, clrGP, preFetchRegs, hp.f4, hp.rme, hF4', hRME', hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]; done)
    | skip
  unfold __CycleEnd
  try simp only [ArmBridge.Awc.ite_cond, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  try simp only [↓bind_app, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  rw [speCycle_frame real]
  rotate_left
  · simp (disch := first | rfl | decide) only [hp.spe, InGuardedPage, Regs.ref_Bool, Regs.ref_BitVec_32, Regs.ref_BitVec_64, Regs.ref_Int, Regs.ref_BitVec_4, __currentCond, __ThisInstr, __ThisInstrEnc, __ExclusiveMonitorSet, __BranchTaken, SEE, PSTATE, _PC, fetchRegs, clrGP, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Sail.ConcurrencyInterfaceV1.RegMap.set_ne, Sail.ConcurrencyInterfaceV1.RegMap.set_same, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  · simp (disch := first | rfl | decide) only [hp.pmbs, InGuardedPage, Regs.ref_Bool, Regs.ref_BitVec_32, Regs.ref_BitVec_64, Regs.ref_Int, Regs.ref_BitVec_4, __currentCond, __ThisInstr, __ThisInstrEnc, __ExclusiveMonitorSet, __BranchTaken, SEE, PSTATE, _PC, fetchRegs, clrGP, preFetchRegs, Register.__InstructionStep, Register.BTypeCompatible, Sail.ConcurrencyInterfaceV1.RegMap.set_ne, Sail.ConcurrencyInterfaceV1.RegMap.set_same, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  try simp only [↓bind_app, Bool.not_true, hEnc, hIT, hSS, hTaken, hp.f4, hp.rme, hp.spe, hp.el, hp.nrw, hp.e2h, hp.tge, hp.scrns, hp.pmbe, hp.mdss, hp.pmbs, hp.pss]
  unfold nativeAtCounter beforeCounterTakenWithNext
  dsimp only []

/- Current-state tail controls never restrict incoming BTYPE or BTN. -/
def beforeCounterWithNext (next : BitVec 2) (s : NativeState) : NativeState :=
  if s.regs.__BranchTaken then beforeCounterTakenWithNext next s else beforeCounterNotTakenWithNext next s

def beforeCounterCurrent (s : NativeState) : NativeState := beforeCounterWithNext s.regs.BTypeNext s

theorem beforeCounterWithNext_zero (s : NativeState) :
    beforeCounterWithNext 0#2 s = ArmBridge.CruxGenGuarded.beforeCounter s := by
  cases ht : s.regs.__BranchTaken <;> rfl

theorem epilogue_current_boundary (real : Type) [Sail.SailReal real] (s : NativeState) (hp : EntryPins s)
    (hEnc : s.regs.__ThisInstrEnc = .__A64)
    (hEret : (Sail.BitVec.extractLsb (s.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false)
    (hIT : s.regs.ShouldAdvanceIT = false) (hSS : s.regs.ShouldAdvanceSS = true) :
    nativeAfterRetired s = nativeAtCounter (beforeCounterCurrent s) := by
  cases ht : s.regs.__BranchTaken with
  | false =>
    simpa only [beforeCounterCurrent, beforeCounterWithNext, ht, Bool.false_eq_true, ite_false] using
      (epilogue_current_NotTaken real s hp hEnc hEret hIT hSS ht)
  | true =>
    simpa only [beforeCounterCurrent, beforeCounterWithNext, ht, ite_true] using
      (epilogue_current_Taken real s hp hEnc hEret hIT hSS ht)

theorem beforeCounterCurrent_quiet (ticks : Nat) (s : NativeState) (hq : HookQuiet ticks s) :
    HookQuiet ticks (beforeCounterCurrent s) := by
  cases ht : s.regs.__BranchTaken with
  | false =>
    simpa only [beforeCounterCurrent, beforeCounterWithNext, ht, Bool.false_eq_true, ite_false] using
      (beforeCounterNotTakenWithNext_quiet s.regs.BTypeNext ticks s hq)
  | true =>
    simpa only [beforeCounterCurrent, beforeCounterWithNext, ht, ite_true] using
      (beforeCounterTakenWithNext_quiet s.regs.BTypeNext ticks s hq)

theorem beforeCounterCurrent_btype (s : NativeState) :
    (beforeCounterCurrent s).regs.PSTATE.BTYPE = s.regs.BTypeNext := by
  cases ht : s.regs.__BranchTaken <;>
    simp only [beforeCounterCurrent, beforeCounterWithNext, ht, Bool.false_eq_true, ite_false, ite_true,
      beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, BTypeNext]

theorem beforeCounterCurrent_btn (s : NativeState) :
    (beforeCounterCurrent s).regs.BTypeNext = s.regs.BTypeNext := by
  cases ht : s.regs.__BranchTaken <;>
    simp only [beforeCounterCurrent, beforeCounterWithNext, ht, Bool.false_eq_true, ite_false, ite_true,
      beforeCounterTakenWithNext, beforeCounterNotTakenWithNext]

theorem beforeCounterCurrent_pins (s : NativeState) (hp : EntryPins s) : EntryPins (beforeCounterCurrent s) := by
  cases ht : s.regs.__BranchTaken <;>
    simp only [beforeCounterCurrent, beforeCounterWithNext, ht, Bool.false_eq_true, ite_false, ite_true] <;>
    constructor
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.f4
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.rme
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.spe
  · rfl
  · rfl
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.edecr
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.cti
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.st
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.edesr
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.btt
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.emu
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.e2h
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.tge
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.scrns
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.pmbe
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.mdss
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.pmbs
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.da
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.di
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.df
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.il
  · rfl
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.f4
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.rme
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.spe
  · rfl
  · rfl
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.edecr
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.cti
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.st
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.edesr
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.btt
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.emu
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.e2h
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.tge
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.scrns
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.pmbe
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.mdss
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.pmbs
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.da
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.di
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.df
  · simpa (disch := decide) only [beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, RegMap.set_ne] using hp.il
  · rfl

theorem scalar_pins (s : NativeState) (hp : EntryPins s)
    (btype : s.regs.PSTATE.BTYPE = 0#2) (btn : s.regs.BTypeNext = 0#2) : StepPins s where
  f4 := hp.f4
  rme := hp.rme
  spe := hp.spe
  el := hp.el
  nrw := hp.nrw
  edecr := hp.edecr
  cti := hp.cti
  st := hp.st
  edesr := hp.edesr
  btt := hp.btt
  emu := hp.emu
  e2h := hp.e2h
  tge := hp.tge
  scrns := hp.scrns
  pmbe := hp.pmbe
  mdss := hp.mdss
  pmbs := hp.pmbs
  da := hp.da
  di := hp.di
  df := hp.df
  il := hp.il
  pss := hp.pss
  btype := btype
  btn := btn

theorem entry_after_E22 (s t : NativeState) (hp : EntryPins s) (hE : E22Frame s.regs t.regs) : EntryPins t := by
  constructor
  · have hf := frame_pres_E22 (fun x : Regs => x.FeatureImpl[4]! = true)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.f4
  · have hf := frame_pres_E22 (fun x : Regs => x.FeatureImpl[232]! = false)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.rme
  · have hf := frame_pres_E22 (fun x : Regs => x.bank_Bool .SPESampleInFlight = false)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.spe
  · have hf := frame_pres_E22 (fun x : Regs => x.PSTATE.EL = 0#2)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.el
  · have hf := frame_pres_E22 (fun x : Regs => x.PSTATE.nRW = 0#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.nrw
  · have hf := frame_pres_E22 (fun x : Regs => _get_EDECR_Type_RCE (x.bank_BitVec_32 .EDECR) = 0#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.edecr
  · have hf := frame_pres_E22 (fun x : Regs => _get_CTIDEVCTL_Type_RCE (x.bank_BitVec_32 .CTIDEVCTL) = 0#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.cti
  · have hf := frame_pres_E22 (fun x : Regs => _get_EDSCR_Type_STATUS (x.bank_BitVec_32 ._EDSCR) = 0b000010#6)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.st
  · have hf := frame_pres_E22 (fun x : Regs => x.bank_BitVec_32 .EDESR = 0#32)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.edesr
  · have hf := frame_pres_E22 (fun x : Regs => x.Branchtypetaken ≠ BranchType.BranchType_RESET)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.btt
  · have hf := frame_pres_E22 (fun x : Regs => x.__emulator_termination_opcode = none)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.emu
  · have hf := frame_pres_E22 (fun x : Regs => _get_HCR_EL2_Type_E2H (x.bank_BitVec_64 .HCR_EL2) = 1#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.e2h
  · have hf := frame_pres_E22 (fun x : Regs => _get_HCR_EL2_Type_TGE (x.bank_BitVec_64 .HCR_EL2) = 1#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.tge
  · have hf := frame_pres_E22 (fun x : Regs => _get_SCR_EL3_Type_NS (x.bank_BitVec_64 .SCR_EL3) = 1#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.scrns
  · have hf := frame_pres_E22 (fun x : Regs => _get_PMBLIMITR_EL1_Type_E (x.bank_BitVec_64 .PMBLIMITR_EL1) = 0#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.pmbe
  · have hf := frame_pres_E22 (fun x : Regs => _get_MDSCR_EL1_Type_SS (x.bank_BitVec_64 .MDSCR_EL1) = 0#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.mdss
  · have hf := frame_pres_E22 (fun x : Regs => Sail.BitVec.extractLsb (x.bank_BitVec_64 .PMBSR_EL1) 17 17 = 0#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.pmbs
  · have hf := frame_pres_E22 (fun x : Regs => x.PSTATE.A = 0#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.da
  · have hf := frame_pres_E22 (fun x : Regs => x.PSTATE.I = 0#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.di
  · have hf := frame_pres_E22 (fun x : Regs => x.PSTATE.F = 0#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.df
  · have hf := frame_pres_E22 (fun x : Regs => x.PSTATE.IL = 0#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.il
  · have hf := frame_pres_E22 (fun x : Regs => x.PSTATE.SS = 0#1)
      (fun x => by simp (disch := decide) only [eraseE22, RegMap.set_ne]) hE
    exact hf.mpr hp.pss

theorem entry_after_end (s : NativeState) (hp : EntryPins s) : EntryPins (nativeEndState s) := by
  constructor
  · simpa (disch := decide) only [nativeEndState, Register.__cycle_count, Regs.ref_Int, RegMap.set_ne] using hp.f4
  · simpa (disch := decide) only [nativeEndState, Register.__cycle_count, Regs.ref_Int, RegMap.set_ne] using hp.rme
  · simpa (disch := decide) only [nativeEndState, Register.__cycle_count, Regs.ref_Int, RegMap.set_ne] using hp.spe
  · simpa (disch := decide) only [nativeEndState, Register.__cycle_count, Regs.ref_Int, RegMap.set_ne] using hp.el
  · simpa (disch := decide) only [nativeEndState, Register.__cycle_count, Regs.ref_Int, RegMap.set_ne] using hp.nrw
  · simpa (disch := decide) only [nativeEndState, Register.__cycle_count, Regs.ref_Int, RegMap.set_ne] using hp.edecr
  · simpa (disch := decide) only [nativeEndState, Register.__cycle_count, Regs.ref_Int, RegMap.set_ne] using hp.cti
  · simpa (disch := decide) only [nativeEndState, Register.__cycle_count, Regs.ref_Int, RegMap.set_ne] using hp.st
  · simpa (disch := decide) only [nativeEndState, Register.__cycle_count, Regs.ref_Int, RegMap.set_ne] using hp.edesr
  · simpa (disch := decide) only [nativeEndState, Register.__cycle_count, Regs.ref_Int, RegMap.set_ne] using hp.btt
  · simpa (disch := decide) only [nativeEndState, Register.__cycle_count, Regs.ref_Int, RegMap.set_ne] using hp.emu
  · simpa (disch := decide) only [nativeEndState, Register.__cycle_count, Regs.ref_Int, RegMap.set_ne] using hp.e2h
  · simpa (disch := decide) only [nativeEndState, Register.__cycle_count, Regs.ref_Int, RegMap.set_ne] using hp.tge
  · simpa (disch := decide) only [nativeEndState, Register.__cycle_count, Regs.ref_Int, RegMap.set_ne] using hp.scrns
  · simpa (disch := decide) only [nativeEndState, Register.__cycle_count, Regs.ref_Int, RegMap.set_ne] using hp.pmbe
  · simpa (disch := decide) only [nativeEndState, Register.__cycle_count, Regs.ref_Int, RegMap.set_ne] using hp.mdss
  · simpa (disch := decide) only [nativeEndState, Register.__cycle_count, Regs.ref_Int, RegMap.set_ne] using hp.pmbs
  · simpa (disch := decide) only [nativeEndState, Register.__cycle_count, Regs.ref_Int, RegMap.set_ne] using hp.da
  · simpa (disch := decide) only [nativeEndState, Register.__cycle_count, Regs.ref_Int, RegMap.set_ne] using hp.di
  · simpa (disch := decide) only [nativeEndState, Register.__cycle_count, Regs.ref_Int, RegMap.set_ne] using hp.df
  · simpa (disch := decide) only [nativeEndState, Register.__cycle_count, Regs.ref_Int, RegMap.set_ne] using hp.il
  · simpa (disch := decide) only [nativeEndState, Register.__cycle_count, Regs.ref_Int, RegMap.set_ne] using hp.pss

theorem beforeCounterCurrent_sys (s : NativeState) (hp : EntryPins s) :
    SysEq2 s.regs (beforeCounterCurrent s).regs := by
  cases ht : s.regs.__BranchTaken <;>
    simp only [beforeCounterCurrent, beforeCounterWithNext, ht, Bool.false_eq_true, ite_false, ite_true,
      beforeCounterTakenWithNext, beforeCounterNotTakenWithNext] <;>
    constructor <;> first | rfl | exact hp.el.symm | exact hp.nrw.symm

theorem beforeCounterCurrent_branch (s : NativeState) :
    BrSysEq s.regs (beforeCounterCurrent s).regs := by
  cases ht : s.regs.__BranchTaken <;>
    simp only [beforeCounterCurrent, beforeCounterWithNext, ht, Bool.false_eq_true, ite_false, ite_true,
      beforeCounterTakenWithNext, beforeCounterNotTakenWithNext] <;> constructor <;> rfl

theorem beforeCounterCurrent_output (s : NativeState) : CongOut (beforeCounterCurrent s) s := by
  cases ht : s.regs.__BranchTaken <;>
    simp only [beforeCounterCurrent, beforeCounterWithNext, ht, Bool.false_eq_true, ite_false, ite_true,
      beforeCounterTakenWithNext, beforeCounterNotTakenWithNext] <;> constructor <;> rfl

theorem beforeCounterCurrent_nonProj (s : NativeState) (hp : EntryPins s) :
    ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap s.regs (beforeCounterCurrent s).regs := by
  cases ht : s.regs.__BranchTaken <;>
    simp (disch := decide) only [beforeCounterCurrent, beforeCounterWithNext, ht, Bool.false_eq_true, ite_false, ite_true,
      ArmCertCT.CT2.NonProjRegsEq, ArmCertCT.CT2.mask, ArmCertCT.CT2.maskPSTATE,
      beforeCounterTakenWithNext, beforeCounterNotTakenWithNext, ArmBridge.CruxNonProj.maskBank_set, hp.el, hp.nrw, hp.pss]

theorem beforeCounterCurrent_events (s : NativeState) : (beforeCounterCurrent s).events = s.events := by
  cases ht : s.regs.__BranchTaken <;>
    simp only [beforeCounterCurrent, beforeCounterWithNext, ht, Bool.false_eq_true, ite_false, ite_true,
      beforeCounterTakenWithNext, beforeCounterNotTakenWithNext]

theorem beforeCounterCurrent_dit (s : NativeState) : (beforeCounterCurrent s).regs.PSTATE.DIT = s.regs.PSTATE.DIT := by
  cases ht : s.regs.__BranchTaken <;>
    simp only [beforeCounterCurrent, beforeCounterWithNext, ht, Bool.false_eq_true, ite_false, ite_true,
      beforeCounterTakenWithNext, beforeCounterNotTakenWithNext]

theorem beforeCounterCurrent_gic (s : NativeState) : (beforeCounterCurrent s).regs.bank_Option_InterruptID .__GIC_Pending = s.regs.bank_Option_InterruptID .__GIC_Pending := by
  cases ht : s.regs.__BranchTaken <;>
    simp only [beforeCounterCurrent, beforeCounterWithNext, ht, Bool.false_eq_true, ite_false, ite_true,
      beforeCounterTakenWithNext, beforeCounterNotTakenWithNext]

theorem beforeCounterCurrent_pc (s : NativeState) :
    (beforeCounterCurrent s).regs._PC =
      (if s.regs.__BranchTaken then s.regs._PC else s.regs._PC + 4#64) := by
  cases ht : s.regs.__BranchTaken with
  | false =>
    simp only [beforeCounterCurrent, beforeCounterWithNext, ht, Bool.false_eq_true, ite_false]
    exact (pc4 s.regs._PC).symm
  | true => simp only [beforeCounterCurrent, beforeCounterWithNext, ht, ite_true, beforeCounterTakenWithNext]

theorem end_sys (s : NativeState) : SysEq2 s.regs (nativeEndState s).regs := by constructor <;> rfl
theorem end_branch (s : NativeState) : BrSysEq s.regs (nativeEndState s).regs := by constructor <;> rfl

#print axioms beforeCounterWithNext_zero
#print axioms epilogue_current_boundary
#print axioms beforeCounterCurrent_quiet
#print axioms beforeCounterCurrent_btype
#print axioms beforeCounterCurrent_btn
#print axioms beforeCounterCurrent_pins
#print axioms scalar_pins
#print axioms entry_after_E22
#print axioms entry_after_end
#print axioms beforeCounterCurrent_sys
#print axioms beforeCounterCurrent_branch
#print axioms beforeCounterCurrent_output
#print axioms beforeCounterCurrent_nonProj
#print axioms beforeCounterCurrent_events
#print axioms beforeCounterCurrent_dit
#print axioms beforeCounterCurrent_gic
#print axioms beforeCounterCurrent_pc
#print axioms end_sys
#print axioms end_branch

#print axioms epilogue_current_NotTaken
#print axioms epilogue_current_Taken
end ArmBridge.CruxGenGuarded
