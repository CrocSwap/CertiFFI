import Sail.Common
import Sail.IntRange
import Sail.Sail
import Lean.Elab.Command
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace BookkeepingGuard.LoopIndexArithmetic

/- The provider's checked conversion is ordinary `toNat` on its nonnegative domain. -/
run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.LoopIndexArithmetic.toNatChecked_eq_toNat"
  (← IO.getStderr).flush

theorem toNatChecked_eq_toNat (i : Int) (h0 : 0 ≤ i) :
    Sail.Int.toNatChecked i = i.toNat :=
  Sail.Int.toNatChecked_of_nonneg i h0

/- The exact actual loop bounds imply the checked-index cast, strict bounds
and both Boolean guards. No stronger counter or accumulator guard is added. -/
run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.LoopIndexArithmetic.checked_index_facts"
  (← IO.getStderr).flush

theorem checked_index_facts (i counters : Int)
    (h0 : 0 ≤ i) (hi : i ≤ counters - 1) (hc : counters ≤ 31) :
    let n := Sail.Int.toNatChecked i
    (n : Int) = i ∧ n < 31 ∧ (n : Int) < counters ∧
      ((0 ≤b i) && (i ≤b 32)) = true ∧
      ((0 ≤b i) && (i <b 31)) = true := by
  dsimp only
  rw [toNatChecked_eq_toNat i h0]
  have hcast : (i.toNat : Int) = i := by omega
  have h31 : i < 31 := by omega
  have h32 : i ≤ 32 := by omega
  exact ⟨hcast, by omega, by omega, by simp [h0, h32], by simp [h0, h31]⟩

#print axioms toNatChecked_eq_toNat
#print axioms checked_index_facts

end BookkeepingGuard.LoopIndexArithmetic
