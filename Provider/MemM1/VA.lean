import MemM1.S1Callees
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.VA
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality

theorem bit_hi (va : BitVec 64) (hva : va.toNat < 2^48) (i : Nat) (hi : 48 ≤ i) :
    va.getLsbD i = false := by
  simp only [BitVec.getLsbD]
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hva (Nat.pow_le_pow_right (by decide) hi))

theorem and_hi (va C : BitVec 64) (hva : va.toNat < 2^48)
    (hC : ∀ i < 48, C.getLsbD i = false) : va &&& C = 0#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_zero]
  by_cases h : i < 48
  · rw [hC i h, Bool.and_false]
  · rw [bit_hi va hva i (by omega), Bool.false_and]

theorem upd (va : BitVec 64) : BitVec.updateSubrange va 59 56 0#4 = va &&& 0xF0FFFFFFFFFFFFFF#64 := by
  simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
  exact BitVec.and_comm _ _

theorem cw {n m : Nat} (x : BitVec n) (h : n = m) (i : Nat) :
    (Sail.BitVec.castWidth (m := m) x).getLsbD i = x.getLsbD i := by
  subst h; simp

/-- The output address of a 4K level-3 page with base `B` for the VA `va`:
    the page base with the 12-bit page offset of `va` filled in. -/
def pageOA (B : BitVec 56) (va : BitVec 64) : BitVec 56 := B ||| (va.setWidth 56 &&& 0xfff#56)
/-- A level-3, non-contiguous walk state with NS leaf base `B` (the S1StageOA reference shape). -/
def WB (B : BitVec 56) : TTWState :=
  { (default : TTWState) with
    level := 3
    contiguous := 0#1
    baseaddress := ({paspace := .PAS_NonSecure, address := B} : FullAddress) }

theorem addr_WB0 (B : BitVec 56) (va : BitVec 64) :
    S1StageOA.address va (WB B) = FullAddress.mk .PAS_NonSecure
      (Sail.BitVec.castWidth (n := 56) (m := 56)
        (Sail.BitVec.extractLsb B 55 12 +++ Sail.BitVec.extractLsb va 11 0)) := rfl

theorem addr_WB (B : BitVec 56) (va : BitVec 64) (hB : B &&& 0xfff#56 = 0#56) :
    S1StageOA.address va (WB B) = {paspace := .PAS_NonSecure, address := pageOA B va} := by
  rw [addr_WB0]
  congr 1
  rw [Sail.BitVec.castWidth_eq]
  have hK : ∀ i < 56, (0xfff#56).getLsbD i = decide (i < 12) := by decide
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb := congrArg (fun x => BitVec.getLsbD x i) hB
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero, hK i hi] at hb
  simp only [pageOA, Sail.BitVec.extractLsb, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb,
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_setWidth, hK i hi]
  have hi' : i < 56 := by omega
  by_cases h : i < 12
  · simp [h] at hb
    rw [hb, Bool.false_or]
    simp [hi', h]
  · have e : 12 + (i - 12) = i := by omega
    have e2 : i - 12 < 44 := by omega
    simp [h, e, e2]

theorem varange (va : BitVec 64) (hva : va.toNat < 2^48) :
    AArch64_GetVARange va = .VARange_LOWER := by
  have h55 : va[55]! = false :=
    (show va[55]! = va.getLsbD 55 from rfl).trans (bit_hi va hva 55 (by decide))
  have ha : BitVec.access va 55 = 0#1 := by unfold BitVec.access; rw [h55]; rfl
  unfold AArch64_GetVARange
  rw [ha]
  rfl

theorem oorV (va : BitVec 64) (hva : va.toNat < 2^48) (acctype : AccessType) (wp : S1TTWParams)
    (htx : wp.txsz = 16#6) :
    AArch64_VAIsOutOfRange va acctype .Regime_EL20 wp = false := by
  have hva' : (BitVec.updateSubrange va 59 56 0#4).toNat < 2^48 := by
    rw [upd, BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_left hva
  have hM63 : (slice_mask (n := 64) 48 16 : BitVec 64) = 0xFFFF000000000000#64 := by decide
  have hM55 : (slice_mask (n := 64) 48 8 : BitVec 64) = 0x00FF000000000000#64 := by decide
  have c63 : ∀ i < 48, (0xFFFF000000000000#64).getLsbD i = false := by decide
  have c55 : ∀ i < 48, (0x00FF000000000000#64).getLsbD i = false := by decide
  have z1 := and_hi va _ hva c63
  have z2 := and_hi va _ hva c55
  have z3 := and_hi _ _ hva' c63
  have z4 := and_hi _ _ hva' c55
  have hz : (extzv 0#1 : BitVec 64) = 0#64 := by decide
  have hlu : (VARange.VARange_LOWER == VARange.VARange_UPPER) = false := rfl
  have hll : (VARange.VARange_LOWER == VARange.VARange_LOWER) = true := rfl
  have hr : (Regime.Regime_EL20 == Regime.Regime_EL20) = true := rfl
  unfold AArch64_VAIsOutOfRange
  rw [htx]
  cases hm : (wp.mtx == 1#1) <;> cases hb : (wp.tbid == 1#1) <;> cases hi : (wp.tbi == 1#1) <;>
  cases hI : (acctype == AccessType.AccessType_IFETCH) <;>
  simp [AArch64_AddrTop, AArch64_IASize, HasUnprivileged, is_zero_subrange, hm, hb, hi, hI,
    varange va hva, varange _ hva', hM63, hM55, hz, z1, z2, z3, z4, hlu, hll, hr]

/-- StageOA at an arbitrary VA, for a level-3 non-contiguous 4K leaf with 4K-aligned NS base `B`. -/
theorem oaV (va : BitVec 64) (wp : S1TTWParams) (w : TTWState) (s : State) (B : BitVec 56)
    (hd : wp.d128 = 0#1) (htg : wp.tgx = .TGx_4KB) (hl : w.level = 3) (hc : w.contiguous = 0#1)
    (hb : w.baseaddress = {paspace := .PAS_NonSecure, address := B})
    (hB : B &&& 0xfff#56 = 0#56) :
    ∀ t, Frame s t → ∃ u, StageOA va wp.d128 wp.tgx w t =
      .ok {paspace := .PAS_NonSecure, address := pageOA B va} u ∧ Frame t u := by
  intro t _
  rcases S1StageOA.total va w t (by rw [hl]; decide) with ⟨u, h, f⟩
  refine ⟨u, ?_, f⟩
  rw [hd, htg, h, MemM1.S1Callees.addr_congr va w (WB B) hb hl hc, addr_WB B va hB]

/-- Sanity: at VA 0 and the M1 leaf base, pageOA is the VA-0 output address. -/
theorem pageOA_zero : pageOA 0x505000000#56 0#64 = 0x505000000#56 := by decide

#print axioms varange
#print axioms oorV
#print axioms addr_WB
#print axioms oaV
#print axioms pageOA_zero
end MemM1.VA
