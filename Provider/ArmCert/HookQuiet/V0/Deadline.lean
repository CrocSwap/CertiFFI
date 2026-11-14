import ArmCert.HookQuiet.V0.Predicate
import Lean.Elab.Command
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512

namespace ArmCert.HookQuiet.V0

/- Pure arithmetic support for the actual counter proof. The caller of the
public native theorem does not supply these count-successor relations: the
native owner must prove them from the real ordinary counter transition. -/
run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.Deadline.deadline_after_count_advance"
  (← IO.getStderr).flush

theorem deadline_after_count_advance {ticks : Nat} {r next : ArmFull.Regs}
    {offset compare : BitVec 64}
    (h : Deadline (ticks + 1) r offset compare)
    (hLower : physical r ≤ physical next)
    (hUpper : physical next ≤ physical r + 1) :
    Deadline ticks next offset compare := by
  have hSum : physical next + ticks ≤ physical r + (ticks + 1) := by omega
  exact ⟨Nat.le_trans h.1 hLower,
    Nat.lt_of_le_of_lt hSum h.2.1,
    Nat.lt_of_le_of_lt (Nat.sub_le_sub_right hSum _) h.2.2⟩

/- The horizon endpoint bound also bounds the current non-wrapping effective
count. Relating this Nat subtraction to the actual BitVec offset subtraction
is a separate model/arithmetic obligation. -/
run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.Deadline.deadline_current"
  (← IO.getStderr).flush

theorem deadline_current {ticks : Nat} {r : ArmFull.Regs}
    {offset compare : BitVec 64} (h : Deadline ticks r offset compare) :
    physical r - offset.toNat < compare.toNat := by
  exact Nat.lt_of_le_of_lt
    (Nat.sub_le_sub_right (Nat.le_add_right (physical r) ticks) _) h.2.2

#print axioms deadline_after_count_advance
#print axioms deadline_current

end ArmCert.HookQuiet.V0
