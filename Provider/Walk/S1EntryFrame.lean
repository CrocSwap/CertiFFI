import Walk.S2NextEntryFrame
import Walk.S1Normality
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1EntryFrame
open S1Normality

def Effect (level : Int) (ia : BitVec 64) (table : FullAddress) (s : State) :
    EStateM.Result (Sail.Error exception) State FullAddress → Prop
  | .ok addr t => addr = S2NextEntryFrame.address level ia table ∧ Frame s t
  | .error _ _ => False

theorem effect (level : Int) (skl : BitVec 2) (txsz : BitVec 6)
    (ia : BitVec 64) (table : FullAddress) (s : State)
    (hLevel : 0 ≤ level ∧ level ≤ 3) :
    Effect level ia table s
      (AArch64_TTEntryAddress level 0#1 skl .TGx_4KB txsz ia table s) := by
  rw [S2NextEntryAddress.complete]
  have hc : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;>
    delta S2NextEntryAddress.native <;> simp [Effect, Frame, S2NextEntryFrame.address] <;> rfl

theorem total (level : Int) (skl : BitVec 2) (txsz : BitVec 6)
    (ia : BitVec 64) (table : FullAddress) (s : State)
    (hLevel : 0 ≤ level ∧ level ≤ 3) :
    ∃ t, AArch64_TTEntryAddress level 0#1 skl .TGx_4KB txsz ia table s =
      .ok (S2NextEntryFrame.address level ia table) t ∧ Frame s t := by
  have hf := effect level skl txsz ia table s hLevel
  cases hr : AArch64_TTEntryAddress level 0#1 skl .TGx_4KB txsz ia table s with
  | error err t => simp only [hr, Effect] at hf
  | ok addr t =>
    simp only [hr, Effect] at hf
    rcases hf with ⟨ha, hframe⟩
    subst addr
    exact ⟨t, rfl, hframe⟩
#print axioms total
end S1EntryFrame
