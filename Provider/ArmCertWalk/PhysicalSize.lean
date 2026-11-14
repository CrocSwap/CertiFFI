import ArmCertWalk.Profile
import Walk.S2PhysicalSize

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

/-- The actual source's one discarded integer draw increments occurrence 1478.
All other fields remain those of the supplied actual state. -/
def physicalPost (state : State) : State :=
  { state with choiceOcc := state.choiceOcc.insert 1478 (state.choiceOcc.getD 1478 0 + 1) }

/-- Exact canonical native result, including the actual choice-occurrence state.
No future helper success or output is assumed. -/
theorem physicalSize_eq (config : PhysicalConfig) (state : State)
    (current : PhysicalAt config state) :
    AArch64_PhysicalAddressSize 0#1 config.ips .TGx_4KB state =
      .ok (effectiveBits config) (physicalPost state) := by
  have legal := current.legal
  unfold LegalPAMax at legal
  rw [S2PhysicalSize.complete config.paMax config.ips state current.pa]
  have cases : config.ips = 0#3 ∨ config.ips = 1#3 ∨ config.ips = 2#3 ∨
      config.ips = 3#3 ∨ config.ips = 4#3 ∨ config.ips = 5#3 ∨
      config.ips = 6#3 ∨ config.ips = 7#3 := by
    have bound := config.ips.isLt
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat]
    omega
  rcases cases with ps | ps | ps | ps | ps | ps | ps | ps <;>
    cases lpa : config.lpa <;> cases lpa2 : config.lpa2 <;>
    simp [S2PhysicalSize.native, S2PhysicalSize.native0, S2PhysicalSize.native1,
      S2PhysicalSize.native2, S2PhysicalSize.native3, S2PhysicalSize.native4,
      S2PhysicalSize.native5, S2PhysicalSize.native6, S2PhysicalSize.native7,
      ps, current.lpa, current.lpa2, lpa, lpa2, legal, effectiveBits,
      encodedBits, formatCap, physicalPost, Int.min_def] <;> omega

theorem physicalSize_total (config : PhysicalConfig) (state : State)
    (current : PhysicalAt config state) :
    ∃ other : State,
      AArch64_PhysicalAddressSize 0#1 config.ips .TGx_4KB state =
        .ok (effectiveBits config) other ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  exact ⟨physicalPost state, physicalSize_eq config state current, rfl, rfl, rfl⟩

#print axioms physicalSize_eq
#print axioms physicalSize_total

end ArmCertWalk
