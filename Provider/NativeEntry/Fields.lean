import Bridge.RootFrame
import Pilot.Driver
import Spike91.NativeActLib
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntry
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false

/- Once-generic register record identity, not an instruction evaluator. -/
theorem btn_set_zero (r : Regs) (zero : r.BTypeNext = 0#2) :
    Register.BTypeNext.set (0#2) r = r := by
  change ({ r with BTypeNext := 0#2 } : Regs) = r
  rw [← zero]

@[step_summary] theorem scr_ns_view (value : BitVec 64) :
    Sail.BitVec.extractLsb (Mk_SCRType value) 0 0 = _get_SCR_EL3_Type_NS value := by rfl

/- Push a success witness through a branch without simplifying its large
native state terms. Branch conditions remain available for local arithmetic. -/
theorem ite_ok {α σ ε : Type} {condition : Prop} [Decidable condition]
    {value : α} {left right : EStateM.Result ε σ α}
    (yes : condition → ∃ state, left = .ok value state)
    (no : ¬ condition → ∃ state, right = .ok value state) :
    ∃ state, (if condition then left else right) = .ok value state := by
  by_cases h : condition
  · simpa only [if_pos h] using yes h
  · simpa only [if_neg h] using no h

#print axioms btn_set_zero
#print axioms scr_ns_view
#print axioms ite_ok
end NativeEntry
