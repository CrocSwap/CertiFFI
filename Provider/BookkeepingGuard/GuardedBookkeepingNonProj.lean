/- Once-generic helper supplied by Isla (source5deaf191, 2026-11-08);
   proof bodies unchanged, compile diagnostics/caps added in Core. -/
import Bridge.CruxGenGuarded.Metadata
import Bridge.CruxGenGuarded.EpilogueNotTaken
import Bridge.CruxGenGuarded.EpilogueTaken
import Bridge.CruxGenGuarded.Cycle
import Bridge.CruxNonProj

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmBridge.CruxNonProj ArmCertCT.CT2
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000

-- d193 split (certiffi): Sail-side content only; the LNSym content moved to BookkeepingGuard.GuardedBookkeepingNonProjLNSym.
namespace BookkeepingGuard.GuardedBookkeepingNonProj


/- The actual metadata state changes only projected/bookkeeping registers. -/
run_cmd do
  IO.eprintln "CURRENT_DECL BookkeepingGuard.actionState_nonProj"
  (← IO.getStderr).flush

theorem actionState_nonProj (w : BitVec 32) (t : NativeState) (K : Int) :
    NonProjRegsEq bkHeap t.regs (actionState w t K).regs := by
  simp (disch := decide) only [NonProjRegsEq, mask, actionState, maskBank_set]

/- The untaken epilogue preserves the full B1 mask under the actual step pins. -/
run_cmd do
  IO.eprintln "CURRENT_DECL BookkeepingGuard.beforeCounterNotTaken_nonProj"
  (← IO.getStderr).flush

theorem beforeCounterNotTaken_nonProj (s : NativeState) (hp : StepPins s) :
    NonProjRegsEq bkHeap s.regs (beforeCounterNotTaken s).regs := by
  unfold beforeCounterNotTaken beforeCounterNotTakenWithNext
  simp (disch := decide) only [NonProjRegsEq, mask, maskPSTATE, maskBank_set, hp.el, hp.nrw, hp.pss]

/- The taken epilogue keeps the actual branch PC; B1 masks that projected PC. -/
run_cmd do
  IO.eprintln "CURRENT_DECL BookkeepingGuard.beforeCounterTaken_nonProj"
  (← IO.getStderr).flush

theorem beforeCounterTaken_nonProj (s : NativeState) (hp : StepPins s) :
    NonProjRegsEq bkHeap s.regs (beforeCounterTaken s).regs := by
  unfold beforeCounterTaken beforeCounterTakenWithNext
  simp (disch := decide) only [NonProjRegsEq, mask, maskPSTATE, maskBank_set, hp.el, hp.nrw, hp.pss]

/- The actual final cycle-count write is a named bookkeeping key. -/
run_cmd do
  IO.eprintln "CURRENT_DECL BookkeepingGuard.nativeEndState_nonProj"
  (← IO.getStderr).flush

theorem nativeEndState_nonProj (s : NativeState) :
    NonProjRegsEq bkHeap s.regs (nativeEndState s).regs := by
  simp (disch := decide) only [NonProjRegsEq, mask, nativeEndState,
    Register.__cycle_count, Regs.ref_Int, maskBank_set]

end BookkeepingGuard.GuardedBookkeepingNonProj

