import Sail
open Sail
namespace S1Descriptor
variable {w : Nat}

/- Local descriptor algebra only. Connecting these operations to actual memory
   writes, PIE permissions, and the complete walk remains a separate obligation. -/
def setAF (d : BitVec w) : BitVec w := Sail.BitVec.update d 10 1#1
def setDirty (d : BitVec w) : BitVec w := Sail.BitVec.update d 7 0#1

theorem update_other (d : BitVec w) (n i : Nat) (b : BitVec 1) (hne : i ≠ n) :
    (Sail.BitVec.update d n b).getLsbD i = d.getLsbD i := by
  have hd : d.getLsbD i = true → i < w := by
    intro h
    by_cases hi : i < w
    · exact hi
    · have hz := BitVec.getLsbD_of_ge d i (Nat.le_of_not_gt hi)
      simp [hz] at h
  have hi : i < n ∨ n < i := by omega
  rcases hi with hi | hi
  · simp [Sail.BitVec.update, Sail.BitVec.updateSubrange', BitVec.zeroExtend,
      BitVec.getLsbD_shiftLeft, hi] <;> exact hd
  · have hni : ¬ i < n := by omega
    have hsub : i - n ≠ 0 := by omega
    have hb : b.getLsbD (i - n) = false :=
      BitVec.getLsbD_of_ge b (i - n) (by omega)
    simp [Sail.BitVec.update, Sail.BitVec.updateSubrange', BitVec.zeroExtend,
      BitVec.getLsbD_shiftLeft, hni, hsub, hb] <;> exact hd

theorem setAF_other (d : BitVec w) (i : Nat) (h : i ≠ 10) :
    (setAF d).getLsbD i = d.getLsbD i := update_other d 10 i 1#1 h
theorem setDirty_other (d : BitVec w) (i : Nat) (h : i ≠ 7) :
    (setDirty d).getLsbD i = d.getLsbD i := update_other d 7 i 0#1 h

def stable (d : BitVec w) : BitVec w :=
  d &&& ~~~((1#w <<< 10) ||| (1#w <<< 7))

theorem setAF_stable (d : BitVec w) : stable (setAF d) = stable d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i = 10
  · subst i; simp [stable, hi]
  · simp only [stable, BitVec.getLsbD_and, setAF_other d i h]

theorem setDirty_stable (d : BitVec w) : stable (setDirty d) = stable d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i = 7
  · subst i; simp [stable, hi]
  · simp only [stable, BitVec.getLsbD_and, setDirty_other d i h]

/- Effective write permission for the non-PIE descriptor path. -/
def writable (ha hd : Bool) (d : BitVec w) : Bool :=
  !d.getLsbD 7 || (ha && hd && d.getLsbD 51)

theorem setDirty_bit (d : BitVec w) : (setDirty d).getLsbD 7 = false := by
  simp [setDirty, Sail.BitVec.update, Sail.BitVec.updateSubrange', BitVec.zeroExtend] <;> omega

theorem setAF_writable (ha hd : Bool) (d : BitVec w) :
    writable ha hd (setAF d) = writable ha hd d := by
  simp only [writable, setAF_other d 7 (by decide), setAF_other d 51 (by decide)]

theorem setDirty_writable (d : BitVec w) (hdbm : d.getLsbD 51 = true) :
    writable true true (setDirty d) = writable true true d := by
  simp only [writable, setDirty_bit, setDirty_other d 51 (by decide),
    hdbm, Bool.true_and, Bool.or_true, Bool.not_false]

theorem update_address (d : BitVec w) (n width : Nat) (b : BitVec 1)
    (hn : n < 12) :
    (Sail.BitVec.update d n b).extractLsb' 12 width = d.extractLsb' 12 width := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb']
  rw [update_other d n (12 + i) b (by omega)]

structure View (w : Nat) where
  stable : BitVec w
  writable : Bool
  deriving DecidableEq

def view (ha hd : Bool) (d : BitVec w) : View w := ⟨stable d, writable ha hd d⟩

theorem setAF_view (ha hd : Bool) (d : BitVec w) :
    view ha hd (setAF d) = view ha hd d := by
  simp only [view, setAF_stable, setAF_writable]

theorem setDirty_view (d : BitVec w) (hdbm : d.getLsbD 51 = true) :
    view true true (setDirty d) = view true true d := by
  simp only [view, setDirty_stable, setDirty_writable d hdbm]

def hardwareUpdate (af dirty : Bool) (d : BitVec w) : BitVec w :=
  let d := if af then setAF d else d
  if dirty then setDirty d else d

theorem hardwareUpdate_view (ha hd af dirty : Bool) (d : BitVec w)
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

#print axioms update_other
#print axioms setAF_stable
#print axioms setDirty_stable
#print axioms setDirty_writable
#print axioms update_address
#print axioms hardwareUpdate_view
end S1Descriptor
