import ArmCertWalk.AttributeMeaning
import Walk.S2Shareability

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

def ShareabilityEffect (sh : BitVec 2) (state : State) :
    EStateM.Result (Sail.Error exception) State Shareability → Prop
  | .ok value other => ShareabilityAllowed sh value ∧ other.regs = state.regs ∧
      other.mem = state.mem ∧ other.events = state.events
  | .error _ _ => False

theorem shareability_effect (sh : BitVec 2) (state : State) :
    ShareabilityEffect sh state (DecodeShareability sh state) := by
  have possibilities : sh = 0#2 ∨ sh = 1#2 ∨ sh = 2#2 ∨ sh = 3#2 := by
    have bound := sh.isLt
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat]
    omega
  rw [S2Shareability.complete]
  rcases possibilities with rfl | rfl | rfl | rfl <;>
    simp [ShareabilityEffect, ShareabilityAllowed, S2Shareability.native,
      S2Shareability.choose, S2Shareability.value, S2Shareability.occ,
      S2Shareability.native0, S2Shareability.native2, S2Shareability.native3]

theorem shareability_total (sh : BitVec 2) (state : State) :
    ∃ value other, DecodeShareability sh state = .ok value other ∧
      ShareabilityAllowed sh value ∧ other.regs = state.regs ∧ other.mem = state.mem ∧
      other.events = state.events := by
  have effect := shareability_effect sh state
  cases actual : DecodeShareability sh state with
  | error err other => simp only [actual, ShareabilityEffect] at effect
  | ok value other => exact ⟨value, other, rfl, by simpa only [actual, ShareabilityEffect] using effect⟩

#print axioms shareability_effect
#print axioms shareability_total

end ArmCertWalk
