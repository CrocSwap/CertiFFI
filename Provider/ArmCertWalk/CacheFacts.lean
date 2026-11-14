import ArmCertWalk.AttributeMeaning
import ArmCertWalk.CacheSource

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace ArmCertWalk

def CacheEffect (nibble : BitVec 4) (state : State) :
    EStateM.Result (Sail.Error exception) State MemAttrHints → Prop
  | .ok cache other => cacheProjection cache = decodedCache nibble ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events
  | .error _ _ => False

/-- One finite semantic proof for every cache nibble. Unknown fields are erased
only where the source leaves them inactive. No native result is an input. -/
theorem cache_effect (nibble : BitVec 4) (state : State) :
    CacheEffect nibble state (DecodeLDFAttr nibble state) := by
  have possibilities : nibble = 0#4 ∨ nibble = 1#4 ∨ nibble = 2#4 ∨ nibble = 3#4 ∨
      nibble = 4#4 ∨ nibble = 5#4 ∨ nibble = 6#4 ∨ nibble = 7#4 ∨
      nibble = 8#4 ∨ nibble = 9#4 ∨ nibble = 10#4 ∨ nibble = 11#4 ∨
      nibble = 12#4 ∨ nibble = 13#4 ∨ nibble = 14#4 ∨ nibble = 15#4 := by
    have bound := nibble.isLt
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat]
    omega
  rw [CacheSource.complete]
  rcases possibilities with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [CacheSource.native, CacheEffect, cacheProjection, decodedCache, cachePolicy, cacheHints,
      MemAttr_NC, MemAttr_WT, MemAttr_WB, MemHint_No, MemHint_WA, MemHint_RA, MemHint_RWA,
      Sail.BitVec.extractLsb, BitVec.extractLsb, Sail.BitVec.access, BitVec.join1] <;> decide

theorem cache_total (nibble : BitVec 4) (state : State) :
    ∃ cache other, DecodeLDFAttr nibble state = .ok cache other ∧
      cacheProjection cache = decodedCache nibble ∧ other.regs = state.regs ∧
      other.mem = state.mem ∧ other.events = state.events := by
  have effect := cache_effect nibble state
  cases actual : DecodeLDFAttr nibble state with
  | error err other => simp only [actual, CacheEffect] at effect
  | ok cache other => exact ⟨cache, other, rfl, by simpa only [actual, CacheEffect] using effect⟩

#print axioms cache_effect
#print axioms cache_total

end ArmCertWalk
