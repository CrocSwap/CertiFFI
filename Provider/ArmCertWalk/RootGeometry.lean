import ArmCertWalk.RootLayoutBinding

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

theorem floor_div_nine (value : Int) : fdiv_int value 9 = value / 9 := by
  by_cases negative : value < 0
  · simp [fdiv_int, negative, Int.tdiv_eq_ediv, Int.dvd_iff_emod_eq_zero, Int.sign]
    split <;> simp_all <;> omega
  · have nonnegative : 0 ≤ value := by omega
    simp [fdiv_int, negative, Int.tdiv_eq_ediv_of_nonneg nonnegative]


theorem current_root_geometry (layout : S1LogicalReference.Layout) (params : S1TTWParams)
    (va : BitVec 64) (registers : Regs) (current : CurrentLayoutAt layout params va registers)
    (level : layout.start ≤ 3) :
    1 ≤ S1LogicalReference.rootBits layout.start layout.inputBits ∧
    S1LogicalReference.rootBits layout.start layout.inputBits ≤ 9 ∧
    rootTableSize params =
      (S1LogicalReference.rootBits layout.start layout.inputBits : Int) + 3 := by
  have width := params.txsz.isLt
  have input := current.inputBits
  have start := current.start
  change (layout.inputBits : Int) = 64 - (params.txsz.toNat : Int) at input
  simp only [rootStartLevel, floor_div_nine, AArch64_IASize] at start
  have rootBounds : 1 ≤ layout.inputBits - (12 + 9 * (3 - layout.start)) ∧
      layout.inputBits - (12 + 9 * (3 - layout.start)) ≤ 9 := by omega
  refine ⟨rootBounds.1, rootBounds.2, ?_⟩
  unfold rootTableSize
  rw [← current.start, ← current.inputBits]
  unfold S1LogicalReference.rootBits
  omega

#print axioms current_root_geometry

end ArmCertWalk
