import Walk.S1MAIRAttr
import Walk.S1KernelMemAttrsFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1MAIRKernel
abbrev State := SequentialState Regs oracleChoiceSource
def index (d : BitVec 64) : Int :=
  (0#1 +++ (Sail.BitVec.extractLsb d 4 2)).toNat
theorem index_bounds (d : BitVec 64) : 0 ≤ index d ∧ index d < 8 := by
  have h := (Sail.BitVec.extractLsb d 4 2).isLt
  have hi : index d = ((Sail.BitVec.extractLsb d 4 2).toNat : Int) := by
    change (((0 : Nat) <<< 3 ||| (Sail.BitVec.extractLsb d 4 2).toNat) : Int) = _
    simp
  rw [hi]
  simp at h
  omega
def value (index : Int) : BitVec 8 :=
  if index = 0 ∨ index = 1 then 255#8 else
  if index = 2 then 68#8 else
  if index = 4 then 4#8 else 0#8

theorem valid (index : Int) : S1KernelMemAttrsFrame.Valid (value index) := by
  unfold value
  split <;> simp_all [S1KernelMemAttrsFrame.Valid]
  split <;> simp_all [S1KernelMemAttrsFrame.Valid]
  split <;> simp_all [S1KernelMemAttrsFrame.Valid]

/- Both C34 kernel-base recipes use these eight ordinary MAIR slots.
   MAIR2, feature state, memory, registers and choice oracle stay arbitrary. -/
theorem total (index : Int) (mair2 : BitVec 64) (s : State)
    (hIndex : 0 ≤ index ∧ index < 8) :
    AArch64_MAIRAttr index mair2 0x000000040044ffff#64 s = .ok (value index) s := by
  have hc : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 ∨ index = 6 ∨ index = 7 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [S1MAIRAttr.complete] <;>
    delta S1MAIRAttr.native <;> simp [value] <;> rfl
#print axioms total
#print axioms valid
#print axioms index_bounds
end S1MAIRKernel
