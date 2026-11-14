import Walk.S1LeafBase
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1LeafBaseFrame
abbrev State := SequentialState Regs oracleChoiceSource
def base (d : BitVec 64) (level : Int) : BitVec 56 :=
  let size := Sail.Int.toNatChecked (12 + 9 * (3 - level))
  Sail.BitVec.updateSubrange (0#56) 47 0
    (Sail.BitVec.castWidth (m := 48) ((Sail.BitVec.extractLsb d 47 size) +++ (0#size)))
theorem total (d : BitVec 64) (level : Int) (s : State)
    (hLevel : 0 ≤ level ∧ level ≤ 3) :
    AArch64_LeafBase d 0#1 0#1 .TGx_4KB level s = .ok (base d level) s := by
  rw [S1LeafBase.complete]
  have hc : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;>
    delta S1LeafBase.native <;> simp [base, TGxGranuleBits, FINAL_LEVEL, Zeros] <;> rfl
#print axioms total
end S1LeafBaseFrame
