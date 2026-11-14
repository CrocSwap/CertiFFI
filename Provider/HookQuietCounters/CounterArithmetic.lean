import HookQuietCounters.Timer
import ArmCert.HookQuiet.V0.Deadline
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.CounterArithmetic.extract_updated"
  (← IO.getStderr).flush

theorem extract_updated {w hi lo : Nat} (x : BitVec w) (y : BitVec (hi-lo+1))
    (hfit : hi < w) (horder : lo ≤ hi) :
    Sail.BitVec.extractLsb (Sail.BitVec.updateSubrange x hi lo y) hi lo = y := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi'
  have hw : lo + i < w := by omega
  have hl : ¬lo + i < lo := by omega
  have hy : lo + i - lo < hi - lo + 1 := by omega
  simp [Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
    BitVec.zeroExtend, hw, hl, hy, hi']

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CounterArithmetic.update_low_bit"
  (← IO.getStderr).flush

theorem update_low_bit {w hi lo i : Nat} (x : BitVec w) (y : BitVec (hi-lo+1))
    (hfit : i < w) (hlow : i < lo) :
    (Sail.BitVec.updateSubrange x hi lo y).getLsbD i = x.getLsbD i := by
  simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.zeroExtend,
    hfit, hlow]

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CounterArithmetic.advanceCount"
  (← IO.getStderr).flush

def advanceCount (s : NativeState) : NativeState :=
  let count := Sail.BitVec.updateSubrange s.regs.PhysicalCount 87 24
    (BitVec.addInt (Sail.BitVec.extractLsb s.regs.PhysicalCount 87 24) 1)
  let r : Regs := {s.regs with PhysicalCount := count}
  {s with regs := r}

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CounterArithmetic.physical_advance"
  (← IO.getStderr).flush

theorem physical_advance (s : NativeState) :
    physicalValue (advanceCount s) = BitVec.addInt (physicalValue s) 1 := by
  exact extract_updated (w := 88) (hi := 87) (lo := 24) s.regs.PhysicalCount
    (BitVec.addInt (physicalValue s) 1) (by decide) (by decide)

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CounterArithmetic.advance_no_wrap"
  (← IO.getStderr).flush

theorem advance_no_wrap (budget : Nat) (s : NativeState)
    (h : ArmCert.HookQuiet.V0.physical s.regs + (budget+1) < 2^64) :
    ArmCert.HookQuiet.V0.physical s.regs ≤ ArmCert.HookQuiet.V0.physical (advanceCount s).regs ∧
    ArmCert.HookQuiet.V0.physical (advanceCount s).regs ≤ ArmCert.HookQuiet.V0.physical s.regs + 1 := by
  change (physicalValue s).toNat ≤ (physicalValue (advanceCount s)).toNat ∧
    (physicalValue (advanceCount s)).toNat ≤ (physicalValue s).toNat + 1
  rw [physical_advance]
  have hsmall : (physicalValue s).toNat + 1 < 2^64 := by
    change (physicalValue s).toNat + (budget+1) < 2^64 at h
    omega
  simp [BitVec.addInt, BitVec.toNat_add, Nat.mod_eq_of_lt hsmall]

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CounterArithmetic.timer_deadline"
  (← IO.getStderr).flush

theorem timer_deadline (ticks : Nat) (s : NativeState) (offset compare : BitVec 64)
    (mask : BitVec 1) (irq : InterruptID)
    (h : ArmCert.HookQuiet.V0.Deadline ticks s.regs offset compare) :
    (IsTimerConditionMet offset compare mask irq : SailM Bool) s = .ok false s := by
  apply timer_future
  have hle : offset ≤ physicalValue s := h.1
  rw [BitVec.toNat_sub_of_le hle]
  exact ArmCert.HookQuiet.V0.deadline_current h

#print axioms extract_updated
#print axioms update_low_bit
#print axioms physical_advance
#print axioms advance_no_wrap
#print axioms timer_deadline

end HookQuietCounters
