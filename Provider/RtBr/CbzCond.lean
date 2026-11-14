-- RtBr.CbzCond: Sail-native CBZ frames, d194-clean (BR8.CBZ root + Pilot simp; no projectM).
import BR8.CBZ
import SDKPA.BranchPins
import SDKPA.BranchPinsF
import Crypto.BrSimp
import Pilot.ObservationSimp
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
set_option autoImplicit false
namespace RtBr.CbzCond

theorem xcast (x : BitVec 64) : BitVec.extractLsb 63 0 x = x := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb, BitVec.extractLsb'_toNat]

theorem cond_iff (x : BitVec 64) :
    IsZero (BitVec.castWidth (m := Int.toNatChecked 64)
      (Sail.BitVec.extractLsb x (Int.toNatChecked ((Int.toNatChecked 64 : Int) - 1)) 0)) = true ↔ x = 0#64 := by
  constructor
  · intro h
    simp [IsZero, BitVec.castWidth, Sail.BitVec.extractLsb, Int.toNatChecked, Sail.Int.toNatChecked,
      Sail.BitVec.length] at h
    simp only [BEq.beq, decide_eq_true_eq] at h
    rwa [xcast] at h
  · intro h; subst h; decide

end RtBr.CbzCond
