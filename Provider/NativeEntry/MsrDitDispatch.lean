import Pilot.Driver
import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntry.MsrDit.Dispatch
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
/- GENERATED fixed selector specialization of the actual official dispatch.
No copied dispatch body, replacement evaluator or assumed leaf success. -/
def word (Rt : BitVec 5) : BitVec 32 :=
  0xd51b42a0#32 ||| Rt.setWidth 32
theorem word_not_br : ∀ Rt : BitVec 5,
    Sail.BitVec.extractLsb (word Rt) 31 25 ≠ 107#7 := by decide +kernel
theorem word_not_bti : ∀ Rt : BitVec 5,
    Sail.BitVec.extractLsb (word Rt) 21 12 ≠ 50#10 := by decide +kernel
#print axioms word_not_br
#print axioms word_not_bti

@[step_summary] theorem selector0 (el : BitVec 2) (t : Int)
    (s : SequentialState Regs oracleChoiceSource) :
    (AArch64_AutoGen_SysRegWrite__seg0 el 3#2 3#3 4#4 5#3 2#4 t : SailM Bool) s =
      (pure true : SailM Bool) s := by rfl
#print axioms selector0

@[step_summary] theorem selector1 (el : BitVec 2) (t : Int)
    (s : SequentialState Regs oracleChoiceSource) :
    (AArch64_AutoGen_SysRegWrite__seg1 el 3#2 3#3 4#4 5#3 2#4 t : SailM Bool) s =
      (pure true : SailM Bool) s := by rfl
#print axioms selector1

@[step_summary] theorem selector2 (el : BitVec 2) (t : Int)
    (s : SequentialState Regs oracleChoiceSource) :
    (AArch64_AutoGen_SysRegWrite__seg2 el 3#2 3#3 4#4 5#3 2#4 t : SailM Bool) s =
      (pure true : SailM Bool) s := by rfl
#print axioms selector2

@[step_summary] theorem selector3 (el : BitVec 2) (t : Int)
    (s : SequentialState Regs oracleChoiceSource) :
    (AArch64_AutoGen_SysRegWrite__seg3 el 3#2 3#3 4#4 5#3 2#4 t : SailM Bool) s =
      (pure true : SailM Bool) s := by rfl
#print axioms selector3

@[step_summary] theorem selector4 (el : BitVec 2) (t : Int)
    (s : SequentialState Regs oracleChoiceSource) :
    (AArch64_AutoGen_SysRegWrite__seg4 el 3#2 3#3 4#4 5#3 2#4 t : SailM Bool) s =
      (do DIT_SysRegWrite_cb82290c1722296d el 3#2 3#3 4#4 5#3 2#4 t; pure false : SailM Bool) s := by rfl
#print axioms selector4

@[step_summary] theorem selector_main (el : BitVec 2) (t : Int)
    (s : SequentialState Regs oracleChoiceSource) :
    (AArch64_AutoGen_SysRegWrite el 3#2 3#3 4#4 5#3 2#4 t : SailM Unit) s =
      (DIT_SysRegWrite_cb82290c1722296d el 3#2 3#3 4#4 5#3 2#4 t : SailM Unit) s := by

  have e0 : (AArch64_AutoGen_SysRegWrite__seg0 el 3#2 3#3 4#4 5#3 2#4 t : SailM Bool) =
      (pure true : SailM Bool) := by funext u; exact selector0 el t u

  have e1 : (AArch64_AutoGen_SysRegWrite__seg1 el 3#2 3#3 4#4 5#3 2#4 t : SailM Bool) =
      (pure true : SailM Bool) := by funext u; exact selector1 el t u

  have e2 : (AArch64_AutoGen_SysRegWrite__seg2 el 3#2 3#3 4#4 5#3 2#4 t : SailM Bool) =
      (pure true : SailM Bool) := by funext u; exact selector2 el t u

  have e3 : (AArch64_AutoGen_SysRegWrite__seg3 el 3#2 3#3 4#4 5#3 2#4 t : SailM Bool) =
      (pure true : SailM Bool) := by funext u; exact selector3 el t u

  have e4 : (AArch64_AutoGen_SysRegWrite__seg4 el 3#2 3#3 4#4 5#3 2#4 t : SailM Bool) =
      (do DIT_SysRegWrite_cb82290c1722296d el 3#2 3#3 4#4 5#3 2#4 t; pure false : SailM Bool) := by funext u; exact selector4 el t u

  unfold AArch64_AutoGen_SysRegWrite
  rw [e0, e1, e2, e3, e4]
  simp only [bind, Bind.bind, EStateM.bind, pure, EStateM.pure, ite_true, ite_false]
  cases h : (DIT_SysRegWrite_cb82290c1722296d el 3#2 3#3 4#4 5#3 2#4 t : SailM Unit) s with
  | ok v u => cases v; simp [h, Bind.bind, EStateM.bind, EStateM.pure]
  | error e u => simp [h, Bind.bind, EStateM.bind, EStateM.pure]
#print axioms selector_main
end NativeEntry.MsrDit.Dispatch
