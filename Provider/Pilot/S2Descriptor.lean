import Sail
open Sail
namespace S2Descriptor
/- These are exactly the bit updates in FINAL AArch64_S2Translate.
   This module is a local descriptor result, not yet a memory/map invariant. -/
def setAF (d : BitVec 64) : BitVec 64 := Sail.BitVec.update d 10 1#1
def setDirty (d : BitVec 64) : BitVec 64 := Sail.BitVec.update d 7 1#1

theorem update_other (d : BitVec 64) (n i : Nat) (hne : i ≠ n) :
    (Sail.BitVec.update d n 1#1).getLsbD i = d.getLsbD i := by
  have hd : d.getLsbD i = true → i < 64 := by
    intro h
    by_cases hi : i < 64
    · exact hi
    · have hz := BitVec.getLsbD_of_ge d i (Nat.le_of_not_gt hi)
      simp [hz] at h
  have hi : i < n ∨ n < i := by omega
  rcases hi with hi | hi
  · simp [Sail.BitVec.update, Sail.BitVec.updateSubrange', BitVec.zeroExtend,
      BitVec.getLsbD_shiftLeft, hi] <;> exact hd
  · have hni : ¬ i < n := by omega
    have hsub : i - n ≠ 0 := by omega
    simp [Sail.BitVec.update, Sail.BitVec.updateSubrange', BitVec.zeroExtend,
      BitVec.getLsbD_shiftLeft, hni, hsub] <;> exact hd

theorem setAF_other (d : BitVec 64) (i : Nat) (h : i ≠ 10) :
    (setAF d).getLsbD i = d.getLsbD i := update_other d 10 i h
theorem setDirty_other (d : BitVec 64) (i : Nat) (h : i ≠ 7) :
    (setDirty d).getLsbD i = d.getLsbD i := update_other d 7 i h

theorem update_address (d : BitVec 64) (n : Nat) (hn : n < 12) :
    (Sail.BitVec.update d n 1#1).extractLsb' 12 36 = d.extractLsb' 12 36 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb']
  rw [update_other d n (12 + i) (by omega)]

theorem setAF_address (d : BitVec 64) :
    (setAF d).extractLsb' 12 36 = d.extractLsb' 12 36 := update_address d 10 (by decide)
theorem setDirty_address (d : BitVec 64) :
    (setDirty d).extractLsb' 12 36 = d.extractLsb' 12 36 := update_address d 7 (by decide)

/-- Effective S2AP write permission in the non-S2PI 64-bit descriptor path.
    FINAL AArch64_S2ApplyOutputPerms sets S2AP[1] for HA && HD && DBM. -/
def writable (ha hd : Bool) (d : BitVec 64) : Bool :=
  d.getLsbD 7 || (ha && hd && d.getLsbD 51)

theorem setAF_writable (ha hd : Bool) (d : BitVec 64) :
    writable ha hd (setAF d) = writable ha hd d := by
  simp only [writable, setAF_other d 7 (by decide), setAF_other d 51 (by decide)]

theorem setDirty_bit (d : BitVec 64) : (setDirty d).getLsbD 7 = true := by
  simp [setDirty, Sail.BitVec.update, Sail.BitVec.updateSubrange', BitVec.zeroExtend]

theorem setDirty_writable (d : BitVec 64) (hdbm : d.getLsbD 51 = true) :
    writable true true (setDirty d) = writable true true d := by
  simp only [writable, setDirty_bit, Bool.true_and, hdbm, Bool.or_true, Bool.true_or]

theorem setAF_readable (d : BitVec 64) : (setAF d).getLsbD 6 = d.getLsbD 6 :=
  setAF_other d 6 (by decide)
theorem setDirty_readable (d : BitVec 64) : (setDirty d).getLsbD 6 = d.getLsbD 6 :=
  setDirty_other d 6 (by decide)

/-- Descriptor information other than the hardware AF and dirty bits. -/
def stable (d : BitVec 64) : BitVec 64 :=
  d &&& ~~~((1#64 <<< 10) ||| (1#64 <<< 7))

theorem setAF_stable (d : BitVec 64) : stable (setAF d) = stable d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i = 10
  · subst i; simp [stable]
  · simp only [stable, BitVec.getLsbD_and, setAF_other d i h]

theorem setDirty_stable (d : BitVec 64) : stable (setDirty d) = stable d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i = 7
  · subst i; simp [stable]
  · simp only [stable, BitVec.getLsbD_and, setDirty_other d i h]

structure View where
  stable : BitVec 64
  writable : Bool
  deriving DecidableEq

def view (ha hd : Bool) (d : BitVec 64) : View := ⟨stable d, writable ha hd d⟩

theorem setAF_view (ha hd : Bool) (d : BitVec 64) :
    view ha hd (setAF d) = view ha hd d := by
  simp only [view, setAF_stable, setAF_writable]

theorem setDirty_view (d : BitVec 64) (hdbm : d.getLsbD 51 = true) :
    view true true (setDirty d) = view true true d := by
  simp only [view, setDirty_stable, setDirty_writable d hdbm]

def hardwareUpdate (af dirty : Bool) (d : BitVec 64) : BitVec 64 :=
  let d := if af then setAF d else d
  if dirty then setDirty d else d

theorem hardwareUpdate_view (ha hd af dirty : Bool) (d : BitVec 64)
    (hdirty : dirty = true → ha = true ∧ hd = true ∧ d.getLsbD 51 = true) :
    view ha hd (hardwareUpdate af dirty d) = view ha hd d := by
  cases af <;> cases dirty
  · rfl
  · obtain ⟨rfl, rfl, hdbm⟩ := hdirty rfl
    exact setDirty_view d hdbm
  · exact setAF_view ha hd d
  · obtain ⟨rfl, rfl, hdbm⟩ := hdirty rfl
    have hdbm' : (setAF d).getLsbD 51 = true := by
      rw [setAF_other d 51 (by decide)]
      exact hdbm
    exact (setDirty_view (setAF d) hdbm').trans (setAF_view true true d)

#print axioms setAF_address
#print axioms setDirty_address
#print axioms setAF_writable
#print axioms setDirty_writable
#print axioms setAF_view
#print axioms setDirty_view
#print axioms hardwareUpdate_view
end S2Descriptor
