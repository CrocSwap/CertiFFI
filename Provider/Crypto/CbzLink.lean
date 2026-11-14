import Bridge.Proj
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to Crypto.CbzLinkLNSym.
namespace Crypto.CbzLink

theorem iz64 (x : BitVec 64) :
    IsZero (BitVec.castWidth (Sail.BitVec.extractLsb x 63 0) : BitVec 64) = decide (BitVec.setWidth 64 x = BitVec.zero 64) := by
  simp only [IsZero, Zeros, BitVec.castWidth, Sail.BitVec.extractLsb, BitVec.length]
  by_cases h : x = 0#64
  · subst h; decide
  · have h' : ¬ BitVec.setWidth 64 x = BitVec.zero 64 := by simpa using h
    rw [decide_eq_false h']
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro hc; apply h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat hc
    simp at this ⊢
    have hx := x.isLt
    omega

theorem iz32 (x : BitVec 64) :
    IsZero (BitVec.castWidth (Sail.BitVec.extractLsb x 31 0) : BitVec 32) = decide (BitVec.setWidth 32 x = BitVec.zero 32) := by
  simp only [IsZero, Zeros, BitVec.castWidth, Sail.BitVec.extractLsb, BitVec.length]
  by_cases h : BitVec.setWidth 32 x = BitVec.zero 32
  · rw [decide_eq_true h]
    simp only [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    simp at this ⊢
    omega
  · rw [decide_eq_false h]
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro hc; apply h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat hc
    simp at this ⊢
    omega

end Crypto.CbzLink

