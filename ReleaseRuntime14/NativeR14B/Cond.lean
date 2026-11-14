import NativeR14B.Cbz
/-! Bridge lemmas for path guards: TBNZ32 / CBZ32 decoder conditions over the gpr value (ask). -/
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
namespace NativeR14B

theorem tbnz_join (x : BitVec 64) :
    BitVec.join1 [BitVec.access (BitVec.castWidth (Sail.BitVec.extractLsb x (Int.toNatChecked 31) 0) : BitVec 32) 0] =
      BitVec.ofBool (x.getLsbD 0) := by
  simp [BitVec.join1, BitVec.access, Sail.BitVec.extractLsb, BitVec.castWidth, Int.toNatChecked]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h0 : i = 0 := by simp at hi; omega
  subst h0
  simp
  all_goals first | (by_cases h : x[0] = true <;> simp [h]) | (split <;> simp_all) | (generalize x[0] = b; cases b <;> decide)

theorem extract_setWidth (x : BitVec 64) : BitVec.extractLsb 31 0 x = BitVec.setWidth 32 x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h1 : i ≤ 31 := by omega
  have h2 : i < 32 := by omega
  simp [BitVec.getLsbD_setWidth, h1, h2]

theorem cbz_iszero (x : BitVec 64) :
    IsZero (BitVec.castWidth (Sail.BitVec.extractLsb x (Int.toNatChecked 31) 0) : BitVec 32) = true ↔
      x.setWidth 32 = 0#32 := by
  simp [IsZero, Sail.BitVec.extractLsb, BitVec.castWidth, Int.toNatChecked]
  first
    | (show BitVec.extractLsb 31 0 x = 0#32 ↔ _; rw [extract_setWidth])
    | (rw [extract_setWidth]; rfl)
    | (rw [extract_setWidth])


/-- TBNZ32 condition as bit 0 of X[Rt] (the gpr value regVal unfolds to). -/
theorem tbnzBit_iff (Rt : BitVec 5) (s : ArmBridge.Draft.NativeState) :
    tbnzBit Rt s = 1#1 ↔ (s.regs.gpr[(GPRSummary.key Rt.toNat).val]).getLsbD 0 = true := by
  unfold tbnzBit
  rw [tbnz_join]
  cases (s.regs.gpr[(GPRSummary.key Rt.toNat).val]).getLsbD 0 <;> decide

/-- CBZ32 condition as the low 32 bits of X[Rt] being zero. -/
theorem cbz32Cond_iff (Rt : BitVec 5) (s : ArmBridge.Draft.NativeState) :
    cbz32Cond Rt s ↔ (s.regs.gpr[(GPRSummary.key Rt.toNat).val]).setWidth 32 = 0#32 := by
  unfold cbz32Cond
  exact cbz_iszero _

#print axioms tbnzBit_iff
#print axioms cbz32Cond_iff
end NativeR14B
