import Bridge.CruxGenGuarded.ReleaseHeadline
import Bridge.CruxGenGuarded.HeapV2Compose

/-! heap-v2 claim cards: the INSTANTIATION of the plan parameters, and the AT_INSTANTIATION RunChecks decided on it.
The sealed release theorems quantify over the step-offset map `offS` and the step budgets; the deployed program fixes them:
  offS j = shimPC j            (shim prologue, j ≤ 6)
 = offsetOf (j - 7) (body steps 7..364: HeapV2Compose.offsetOf over HeapV2Plan, bound to ELF 032b5400
 text by the plan-binding receipt)
         = shimPC (j - 358)    (shim epilogue, 365..368)
         = 0                   (beyond the run)
  budget = 369, bodyBudget = 362.
Each theorem below is the card's RunCheck predicate with the instance substituted, proved (std3, by evaluation over the
finite plan). The certify receipt binds these theorems to the predicate instances (prop/statement sha) and the binary. -/
namespace HeapV2Card.Instance
open ArmBridge.CruxGenGuarded

def offS (j : Nat) : BitVec 64 :=
  if j ≤ 6 then Release.shimPC j
  else if j ≤ 364 then HeapV2Compose.offsetOf (j - 7)
  else if j ≤ 368 then Release.shimPC (j - 358)
  else 0

def budget : Nat := 369
def bodyBudget : Nat := 362

theorem shim_aligned : ∀ j, j < 11 → (Release.shimPC j).toNat % 4 = 0 := by decide

theorem body_aligned : ∀ k, k < 358 → (HeapV2Compose.offsetOf k).toNat % 4 = 0 := by decide +kernel

/-- card:plan-offsets / `aligned` on the instance. -/
theorem rc_aligned : ∀ (j : Nat), (offS j).toNat % 4 = 0 := by
  intro j
  unfold offS
  split
  · exact shim_aligned j (by omega)
  · split
    · exact body_aligned (j - 7) (by omega)
    · split
      · exact shim_aligned (j - 358) (by omega)
      · decide

/-- card:plan-offsets / `offPre` on the instance. -/
theorem rc_offPre : ∀ (j : Nat), j ≤ 6 → offS j = Release.shimPC j := by
  intro j h
  unfold offS
  rw [if_pos h]

/-- card:plan-offsets / `offPost` on the instance. -/
theorem rc_offPost : ∀ (j : Nat), 365 ≤ j → j ≤ 368 → offS j = Release.shimPC (j - 358) := by
  intro j h1 h2
  unfold offS
  rw [if_neg (by omega), if_neg (by omega), if_pos h2]

/-- card:budget / `room` on the instance. -/
theorem rc_room : 369 ≤ budget := Nat.le_refl _

/-- card:budget / `hbudget7` on the instance. -/
theorem rc_hbudget7 : budget - 7 = bodyBudget := rfl

/-- BodyEntry.hoff (card:plan-offsets in the unbundled cards) on the instance. -/
theorem rc_hoff : offS 7 = HeapV2Compose.offsetOf 0 := by
  unfold offS
  rw [if_neg (by omega), if_pos (by omega)]

#print axioms rc_aligned
#print axioms rc_offPre
#print axioms rc_offPost
#print axioms rc_room
#print axioms rc_hbudget7
#print axioms rc_hoff

end HeapV2Card.Instance
