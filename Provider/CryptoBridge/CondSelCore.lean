import CryptoBridge.AddSubImmCore
import Bridge.StepM
import BridgeV2.BoundaryV2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to CryptoBridge.CondSelCoreLNSym.
namespace CryptoBridge.CondSelCore

/-- The 16 condition codes. -/
theorem bv4_cases (x : BitVec 4) : x = 0#4 ∨ x = 1#4 ∨ x = 2#4 ∨ x = 3#4 ∨ x = 4#4 ∨ x = 5#4 ∨ x = 6#4 ∨ x = 7#4 ∨ x = 8#4 ∨ x = 9#4 ∨ x = 10#4 ∨ x = 11#4 ∨ x = 12#4 ∨ x = 13#4 ∨ x = 14#4 ∨ x = 15#4 := by
  have hx := x.isLt
  rcases (by omega : x.toNat = 0 ∨ x.toNat = 1 ∨ x.toNat = 2 ∨ x.toNat = 3 ∨ x.toNat = 4 ∨ x.toNat = 5 ∨ x.toNat = 6 ∨ x.toNat = 7 ∨ x.toNat = 8 ∨ x.toNat = 9 ∨ x.toNat = 10 ∨ x.toNat = 11 ∨ x.toNat = 12 ∨ x.toNat = 13 ∨ x.toNat = 14 ∨ x.toNat = 15) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    simp [← BitVec.toNat_inj, h]

end CryptoBridge.CondSelCore

