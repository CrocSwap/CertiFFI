import HookQuietCounters.CounterArithmetic
import HookQuietCounters.TimerQueries
import ArmCert.HookQuiet.V0.TransportE22
import Lean.Elab.Command
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512

namespace HookQuietCounters

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CounterPrefix.bind_if"
  (← IO.getStderr).flush

theorem bind_if {m : Type → Type} [Monad m] {α β : Type}
    (p : Prop) [Decidable p] (x y : m α) (f : α → m β) :
    ((if p then x else y) >>= f) = (if p then x >>= f else y >>= f) := by
  split <;> rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CounterPrefix.advance_quiet"
  (← IO.getStderr).flush

theorem advance_quiet (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet (budget+1) s) :
    ArmCert.HookQuiet.V0.HookQuiet budget (advanceCount s) := by
  apply ArmCert.HookQuiet.V0.hookQuiet_after_E22_guarded_advance q
  · rfl
  · constructor <;> exact ⟨rfl, rfl⟩
  · exact advance_no_wrap budget s

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CounterPrefix.ordinaryIncrement"
  (← IO.getStderr).flush

def ordinaryIncrement : SailM Unit := do
  let enabled ← do
    if ← HaveCNTSCExt () then
      let ctl ← readReg CNTCR
      pure (_get_CNTCR_Type_SCEN ctl == 1#1)
    else pure false
  if enabled then
    let count ← readReg PhysicalCount
    let scale ← readReg CNTSCR
    writeReg PhysicalCount (count + Sail.BitVec.castWidth (m := 88) (Sail.BitVec.zeroExtend scale 88))
  else
    let count ← readReg PhysicalCount
    let prior ← readReg PhysicalCount
    writeReg PhysicalCount (Sail.BitVec.updateSubrange count 87 24
      (BitVec.addInt (Sail.BitVec.extractLsb prior 87 24) 1))

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CounterPrefix.ordinary_increment"
  (← IO.getStderr).flush

theorem ordinary_increment (s : NativeState)
    (h : _get_CNTCR_Type_SCEN (s.regs.bank_BitVec_32 .CNTCR) = 0#1) :
    ordinaryIncrement s = .ok () (advanceCount s) := by
  cases hf : featureValue s .FEAT_CNTSC <;>
    simp [ordinaryIncrement, HaveCNTSCExt, feature_apply, bind_app, pure_apply,
      map_apply, read_apply, hf, h]
  all_goals rfl

#print axioms advance_quiet
#print axioms ordinary_increment

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CounterPrefix.afterIncrement"
  (← IO.getStderr).flush

def afterIncrement (prior : BitVec 64) : SailM Unit := do
  let a64 ← HaveAArch64 ()
  if !a64 then AArch32_CheckTimerConditions () else AArch64_CheckTimerConditions ()
  let current ← PhysicalCountInt ()
  TestEventCNTP prior current
  let current ← PhysicalCountInt ()
  TestEventCNTV prior current

/- Kernel equality exposes the real counter prefix, before any totality claim
about the remaining timer/event tail. -/
run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CounterPrefix.counter_factor"
  (← IO.getStderr).flush

theorem counter_factor (s : NativeState) :
    (GenericCounterTick () : SailM Unit) s =
      (do
        let ctl ← readReg CNTCR
        if _get_CNTCR_Type_EN ctl == 0#1 then
          let a64 ← HaveAArch64 ()
          if !a64 then AArch32_CheckTimerConditions () else AArch64_CheckTimerConditions ()
        else
          let prior ← PhysicalCountInt ()
          ordinaryIncrement
          afterIncrement prior : SailM Unit) s := by
  simp only [GenericCounterTick, ordinaryIncrement, afterIncrement, bind_assoc, bind_if, pure_bind]

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CounterPrefix.counter_prefix_quiet"
  (← IO.getStderr).flush

theorem counter_prefix_quiet (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet (budget+1) s) :
    (GenericCounterTick () : SailM Unit) s =
      (if _get_CNTCR_Type_EN (s.regs.bank_BitVec_32 .CNTCR) == 0#1 then
        AArch64_CheckTimerConditions () s
      else afterIncrement (physicalValue s) (advanceCount s)) := by
  rw [counter_factor]
  rcases bit_cases (_get_CNTCR_Type_EN (s.regs.bank_BitVec_32 .CNTCR)) with hEN | hEN <;>
    simp [bind_app, read_apply, hEN, have_a64 s q.a64,
      physical_count_apply, ordinary_increment s q.ordinary]

#print axioms counter_factor
#print axioms counter_prefix_quiet

end HookQuietCounters
