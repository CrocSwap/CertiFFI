import Walk.S1WalkChecks
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmFull.Register
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1BlockCheck
open S1Normality

theorem read_normal {α : Type} (r : RegisterRef α) : Normal (readReg r) := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem feature_normal : Normal (HaveBlockBBM ()) := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem level_key : __IMPDEF_integer "Block BBM support level" =
    (readReg __block_bbm_implemented : SailM Int) := rfl

theorem level_normal : Normal (AArch64_BlockBBMSupportLevel ()) := by
  unfold AArch64_BlockBBMSupportLevel
  apply bind_normal _ _ feature_normal
  intro enabled
  apply ite_normal
  · intro
    unfold __UNKNOWN_integer
    apply bind_normal _ _ (occ_normal 7)
    intro label
    exact S1EL10PermsCallees.int_normal label
  · intro
    rw [level_key]
    exact read_normal _

theorem normal (d : BitVec 64) : Normal (AArch64_BlocknTFaults 0#1 d) := by
  unfold AArch64_BlocknTFaults
  apply bind_normal _ _ feature_normal
  intro enabled
  apply ite_normal
  · intro; exact pure_normal false
  · intro
    simp [ArmFull.assert, PreSail.assert]
    apply bind_normal _ _ level_normal
    intro level
    apply map_normal
    rw [S1WalkChecks.impdef_nt]
    exact pure_normal true
#print axioms normal
end S1BlockCheck
