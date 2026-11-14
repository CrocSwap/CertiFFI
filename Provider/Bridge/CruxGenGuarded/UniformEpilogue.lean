import Bridge.CruxGenGuarded.HookLaws
import Bridge.CruxGenGuarded.BookkeepingTransport
import BookkeepingGuard.GuardedBookkeepingNonProj
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

-- d193 manual overlay (certiffi): simp sets also unfold *WithNext (EpilogueNotTaken WithNext staleness).
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to Bridge.CruxGenGuarded.UniformEpilogueLNSym.
namespace ArmBridge.CruxGenGuarded

/-! GENERATED uniform selection of the two actual native epilogue states.
Both branches use their own compiled proof spine. -/

def beforeCounter (s : NativeState) : NativeState :=
  if s.regs.__BranchTaken then beforeCounterTaken s else beforeCounterNotTaken s

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.epilogue_boundary"
  (← IO.getStderr).flush

theorem epilogue_boundary (real : Type) [Sail.SailReal real] (s : NativeState) (hp : StepPins s)
      (hEnc : s.regs.__ThisInstrEnc = .__A64)
      (hEret : (Sail.BitVec.extractLsb (s.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false)
      (hIT : s.regs.ShouldAdvanceIT = false) (hSS : s.regs.ShouldAdvanceSS = true)
 :
    nativeAfterRetired s = nativeAtCounter (beforeCounter s) := by
  cases ht : s.regs.__BranchTaken with
  | false =>
    simpa only [beforeCounter, ht, Bool.false_eq_true, ite_false] using
      (epilogue_NotTaken real s hp hEnc hEret hIT hSS ht)
  | true =>
    simpa only [beforeCounter, ht, ite_true] using
      (epilogue_Taken real s hp hEnc hEret hIT hSS ht)

theorem beforeCounter_quiet (b : Nat) (s : NativeState) (hq : HookQuiet b s) : HookQuiet b (beforeCounter s) := by
  cases ht : s.regs.__BranchTaken with
  | false =>
    simpa only [beforeCounter, ht, Bool.false_eq_true, ite_false] using
      (beforeCounterNotTaken_quiet b s hq)
  | true =>
    simpa only [beforeCounter, ht, ite_true] using
      (beforeCounterTaken_quiet b s hq)

theorem beforeCounter_pins (s : NativeState) (hp : StepPins s) : StepPins (beforeCounter s) := by
  cases ht : s.regs.__BranchTaken with
  | false =>
    simpa only [beforeCounter, ht, Bool.false_eq_true, ite_false] using
      (epilogue_not_taken_pins s hp)
  | true =>
    simpa only [beforeCounter, ht, ite_true] using
      (epilogue_taken_pins s hp)

theorem beforeCounter_sys (s : NativeState) (hp : StepPins s) : SysEq2 s.regs (beforeCounter s).regs := by
  cases ht : s.regs.__BranchTaken with
  | false =>
    simpa only [beforeCounter, ht, Bool.false_eq_true, ite_false] using
      (epilogue_not_taken_sys s hp)
  | true =>
    simpa only [beforeCounter, ht, ite_true] using
      (epilogue_taken_sys s hp)

theorem beforeCounter_branch (s : NativeState) (hp : StepPins s) : BrSysEq s.regs (beforeCounter s).regs := by
  cases ht : s.regs.__BranchTaken with
  | false =>
    simpa only [beforeCounter, ht, Bool.false_eq_true, ite_false] using
      (epilogue_not_taken_branch s hp)
  | true =>
    simpa only [beforeCounter, ht, ite_true] using
      (epilogue_taken_branch s hp)

theorem beforeCounter_output (s : NativeState) (hp : StepPins s) : CongOut (beforeCounter s) s := by
  cases ht : s.regs.__BranchTaken with
  | false =>
    simpa only [beforeCounter, ht, Bool.false_eq_true, ite_false] using
      (epilogue_not_taken_output s hp)
  | true =>
    simpa only [beforeCounter, ht, ite_true] using
      (epilogue_taken_output s hp)

theorem beforeCounter_events (s : NativeState) : (beforeCounter s).events = s.events := by
  cases ht : s.regs.__BranchTaken with
  | false =>
    simpa only [beforeCounter, ht, Bool.false_eq_true, ite_false] using
      (beforeCounterNotTaken_events s)
  | true =>
    simpa only [beforeCounter, ht, ite_true] using
      (beforeCounterTaken_events s)

theorem beforeCounter_nonProj (s : NativeState) (hp : StepPins s) : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap s.regs (beforeCounter s).regs := by
  cases ht : s.regs.__BranchTaken with
  | false =>
    simpa only [beforeCounter, ht, Bool.false_eq_true, ite_false] using
      (BookkeepingGuard.GuardedBookkeepingNonProj.beforeCounterNotTaken_nonProj s hp)
  | true =>
    simpa only [beforeCounter, ht, ite_true] using
      (BookkeepingGuard.GuardedBookkeepingNonProj.beforeCounterTaken_nonProj s hp)

theorem beforeCounter_dit (s : NativeState) : (beforeCounter s).regs.PSTATE.DIT = s.regs.PSTATE.DIT := by
  cases ht : s.regs.__BranchTaken <;>
    simp only [beforeCounter, ht, Bool.false_eq_true, ite_false, ite_true,
      beforeCounterTaken, beforeCounterNotTaken, beforeCounterTakenWithNext, beforeCounterNotTakenWithNext,
      RegMap.set_ne, RegMap.set_same, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int]

theorem beforeCounter_gic (s : NativeState) : (beforeCounter s).regs.bank_Option_InterruptID .__GIC_Pending = s.regs.bank_Option_InterruptID .__GIC_Pending := by
  cases ht : s.regs.__BranchTaken <;>
    simp only [beforeCounter, ht, Bool.false_eq_true, ite_false, ite_true,
      beforeCounterTaken, beforeCounterNotTaken, beforeCounterTakenWithNext, beforeCounterNotTakenWithNext,
      RegMap.set_ne, RegMap.set_same, Regs.ref_Bool, Regs.ref_BitVec_2, Regs.ref_Int]

theorem beforeCounter_pc (s : NativeState) :
    (beforeCounter s).regs._PC =
      (if s.regs.__BranchTaken then s.regs._PC else s.regs._PC + 4#64) := by
  cases ht : s.regs.__BranchTaken with
  | false =>
    simp only [beforeCounter, ht, Bool.false_eq_true, ite_false]
    exact (beforeCounterNotTaken_pc s).trans (pc4 s.regs._PC).symm
  | true =>
    simp only [beforeCounter, ht, ite_true]
    exact beforeCounterTaken_pc s

end ArmBridge.CruxGenGuarded

