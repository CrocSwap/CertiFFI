-- Generated source-size dispatch by gen/gen_stage_words.py.
import ArmCertWalk.StageWords
import ArmCertWalk.NextTableProjection
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk

theorem stage_address_canonical (va : BitVec 64) (next : TTWState) (level : Nat)
    (positive : 1 ≤ level) (valid : level ≤ 3) (currentLevel : next.level = (level : Int)) :
    (S1StageOA.address va next).address =
      (S1LogicalReference.outputAddress va level next.baseaddress (next.contiguous == 1#1)).address := by
  change StageWords.word next.baseaddress.address va (S1StageOA.span next) = _
  have levels : level = 1 ∨ level = 2 ∨ level = 3 := by omega
  rcases levels with rfl | rfl | rfl
  all_goals rcases bit_zero_or_one next.contiguous with contiguous | contiguous
  · have span : S1StageOA.span next = 30 := by simp [S1StageOA.span, currentLevel, contiguous]
    rw [span]
    simpa [S1LogicalReference.outputAddress, S1LogicalReference.leafBits, contiguous] using
      StageWords.span_30 next.baseaddress.address va
  · have span : S1StageOA.span next = 34 := by simp [S1StageOA.span, currentLevel, contiguous]
    rw [span]
    simpa [S1LogicalReference.outputAddress, S1LogicalReference.leafBits, contiguous] using
      StageWords.span_34 next.baseaddress.address va
  · have span : S1StageOA.span next = 21 := by simp [S1StageOA.span, currentLevel, contiguous]
    rw [span]
    simpa [S1LogicalReference.outputAddress, S1LogicalReference.leafBits, contiguous] using
      StageWords.span_21 next.baseaddress.address va
  · have span : S1StageOA.span next = 25 := by simp [S1StageOA.span, currentLevel, contiguous]
    rw [span]
    simpa [S1LogicalReference.outputAddress, S1LogicalReference.leafBits, contiguous] using
      StageWords.span_25 next.baseaddress.address va
  · have span : S1StageOA.span next = 12 := by simp [S1StageOA.span, currentLevel, contiguous]
    rw [span]
    simpa [S1LogicalReference.outputAddress, S1LogicalReference.leafBits, contiguous] using
      StageWords.span_12 next.baseaddress.address va
  · have span : S1StageOA.span next = 16 := by simp [S1StageOA.span, currentLevel, contiguous]
    rw [span]
    simpa [S1LogicalReference.outputAddress, S1LogicalReference.leafBits, contiguous] using
      StageWords.span_16 next.baseaddress.address va

theorem stage_canonical_total (va : BitVec 64) (next : TTWState) (level : Nat) (state : State) (params : S1TTWParams)
    (d128 : params.d128 = 0#1) (tg : params.tgx = .TGx_4KB)
    (positive : 1 ≤ level) (valid : level ≤ 3) (currentLevel : next.level = (level : Int)) :
    ∃ result other, StageOA va params.d128 params.tgx next state = .ok result other ∧
      result.paspace = next.baseaddress.paspace ∧
      result.address = (S1LogicalReference.outputAddress va level next.baseaddress (next.contiguous == 1#1)).address ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  obtain ⟨other, call, registers, memory, events⟩ := S1StageOA.total va next state (by omega)
  refine ⟨S1StageOA.address va next, other, ?_, rfl,
    stage_address_canonical va next level positive valid currentLevel, registers, memory, events⟩
  simpa only [d128, tg] using call

#print axioms stage_address_canonical
#print axioms stage_canonical_total
end ArmCertWalk
