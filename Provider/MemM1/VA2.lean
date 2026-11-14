import MemM1.VA
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.VA2
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality

/-! `MemM1.VA.oaV` for a level-2 (2 MB block) leaf. -/

/-- The output address of a 2 MB level-2 block with base `B` for the VA `va`: the block base with
    the 21-bit block offset of `va` filled in. -/
def blockOA (B : BitVec 56) (va : BitVec 64) : BitVec 56 := B ||| (va.setWidth 56 &&& 0x1fffff#56)

/-- A level-2, non-contiguous walk state with NS leaf base `B`. -/
def WB2 (B : BitVec 56) : TTWState :=
  { (default : TTWState) with
    level := 2
    contiguous := 0#1
    baseaddress := ({paspace := .PAS_NonSecure, address := B} : FullAddress) }

theorem addr_WB2_0 (B : BitVec 56) (va : BitVec 64) :
    S1StageOA.address va (WB2 B) = FullAddress.mk .PAS_NonSecure
      (Sail.BitVec.castWidth (n := 56) (m := 56)
        (Sail.BitVec.extractLsb B 55 21 +++ Sail.BitVec.extractLsb va 20 0)) := rfl

theorem addr_WB2 (B : BitVec 56) (va : BitVec 64) (hB : B &&& 0x1fffff#56 = 0#56) :
    S1StageOA.address va (WB2 B) = {paspace := .PAS_NonSecure, address := blockOA B va} := by
  rw [addr_WB2_0]
  refine congrArg (FullAddress.mk PASpace.PAS_NonSecure) ?_
  rw [Sail.BitVec.castWidth_eq]
  have hK : ∀ i < 56, (0x1fffff#56).getLsbD i = decide (i < 21) := by decide
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb := congrArg (fun x => BitVec.getLsbD x i) hB
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero, hK i hi] at hb
  simp only [blockOA, Sail.BitVec.extractLsb, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb,
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_setWidth, hK i hi]
  have hi' : i < 56 := by omega
  by_cases h : i < 21
  · simp [h] at hb
    rw [hb, Bool.false_or]
    simp [hi', h]
  · have e : 21 + (i - 21) = i := by omega
    have e2 : i - 21 < 35 := by omega
    simp [h, e, e2]

/-- StageOA at an arbitrary VA, for a level-2 non-contiguous 2 MB block with 2 MB-aligned NS base `B`. -/
theorem oaV2 (va : BitVec 64) (wp : S1TTWParams) (w : TTWState) (s : State) (B : BitVec 56)
    (hd : wp.d128 = 0#1) (htg : wp.tgx = .TGx_4KB) (hl : w.level = 2) (hc : w.contiguous = 0#1)
    (hb : w.baseaddress = {paspace := .PAS_NonSecure, address := B})
    (hB : B &&& 0x1fffff#56 = 0#56) :
    ∀ t, Frame s t → ∃ u, StageOA va wp.d128 wp.tgx w t =
      .ok {paspace := .PAS_NonSecure, address := blockOA B va} u ∧ Frame t u := by
  intro t _
  rcases S1StageOA.total va w t (by rw [hl]; decide) with ⟨u, h, f⟩
  refine ⟨u, ?_, f⟩
  rw [hd, htg, h, MemM1.S1Callees.addr_congr va w (WB2 B) hb hl hc, addr_WB2 B va hB]

#print axioms addr_WB2
#print axioms oaV2
end MemM1.VA2
