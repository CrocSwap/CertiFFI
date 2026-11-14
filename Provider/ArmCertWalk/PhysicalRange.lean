import ArmCertWalk.PhysicalSize

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

theorem oaOutOfRange_eq (config : PhysicalConfig) (address : BitVec 56) (state : State)
    (current : PhysicalAt config state) :
    AArch64_OAOutOfRange address 0#1 config.ips .TGx_4KB state =
      .ok (!is_zero_subrange address 55 (effectiveBits config)) (physicalPost state) := by
  have bounds := effectiveBits_bounds config current.legal
  have below : effectiveBits config < 56 := by omega
  simp [AArch64_OAOutOfRange, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
    physicalSize_eq config state current, below]

theorem oaOutOfRange_total (config : PhysicalConfig) (address : BitVec 56) (state : State)
    (current : PhysicalAt config state) :
    ∃ other : State,
      AArch64_OAOutOfRange address 0#1 config.ips .TGx_4KB state =
        .ok (!is_zero_subrange address 55 (effectiveBits config)) other ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  exact ⟨physicalPost state, oaOutOfRange_eq config address state current, rfl, rfl, rfl⟩

#print axioms oaOutOfRange_eq
#print axioms oaOutOfRange_total

end ArmCertWalk
