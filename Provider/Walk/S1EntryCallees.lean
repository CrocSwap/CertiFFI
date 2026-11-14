import Walk.S1BlockCheck
import Walk.S1LeafBoth
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 150000
namespace S1EntryCallees
open S1Normality

theorem dcache_normal (regime : Regime) (hr : S1LeafBoth.Regimes regime) :
    Normal (AArch64_S1DCacheEnabled regime) := by
  rcases hr with rfl | rfl <;>
    unfold AArch64_S1DCacheEnabled <;>
    apply bind_normal _ _ (S1BlockCheck.read_normal _) <;>
    intro v <;> exact pure_normal _

theorem epd_normal (regime : Regime) (va : BitVec 64) (hr : S1LeafBoth.Regimes regime) :
    Normal (AArch64_S1EPD regime va) := by
  rcases hr with rfl | rfl
  all_goals
    unfold AArch64_S1EPD
    simp only [HasUnprivileged]
    apply bind_normal _ _ (assert_normal _ _ rfl)
    intro u
    apply ite_normal
    · intro h
      apply bind_normal _ _ (S1BlockCheck.read_normal _)
      intro v
      exact pure_normal _
    · intro h
      apply bind_normal _ _ (S1BlockCheck.read_normal _)
      intro v
      exact pure_normal _

theorem mecid_eq (emec : BitVec 1) (regime : Regime) :
    AArch64_TTWalkMECID emec regime .SS_NonSecure = (pure DEFAULT_MECID : SailM (BitVec 16)) := by
  have hn : bne SecurityState.SS_NonSecure SecurityState.SS_Realm = true := by decide
  by_cases h : emec == 0#1 <;> simp [AArch64_TTWalkMECID, h, hn]

theorem start_zero (wp : S1TTWParams) (hd : wp.d128 = 0#1)
    (htg : wp.tgx = .TGx_4KB) (htx : wp.txsz = 16#6) :
    AArch64_S1StartLevel wp = 0 := by
  simp [AArch64_S1StartLevel, AArch64_IASize, TGxGranuleBits, hd, htg, htx, FINAL_LEVEL]
  rfl
#print axioms dcache_normal
#print axioms epd_normal
#print axioms mecid_eq
#print axioms start_zero
end S1EntryCallees
