import ArmCertWalk.AttributeMeaning

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

theorem device_eq (bits : BitVec 2) (state : State) :
    DecodeDevice bits state = .ok (deviceKind bits) state := by
  have possibilities : bits = 0#2 ∨ bits = 1#2 ∨ bits = 2#2 ∨ bits = 3#2 := by
    have bound := bits.isLt
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat]
    omega
  rcases possibilities with rfl | rfl | rfl | rfl <;>
    simp [DecodeDevice, deviceKind, Pure.pure, EStateM.pure]

attribute [step_summary] device_eq
#print axioms device_eq

end ArmCertWalk
