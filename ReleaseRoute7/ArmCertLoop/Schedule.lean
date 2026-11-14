import ArmCertLoop.Chain

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

namespace ArmCertLoop.Schedule

/-! Public arithmetic schedules. Each is a constant-size function of a
symbolic length, never a generated/unrolled length-n SSA plan. Connecting
them to actual branch outcomes is a separate native instruction obligation. -/

def copySteps (n : Nat) : Nat := if n = 0 then 2 else 6 * n + 3

def copyWordOffset (n k : Nat) : Nat :=
  if k = 0 then 0 else if n = 0 then 32 else if k = 1 then 4
  else if k < 6 * n + 2 then 8 + 4 * ((k - 2) % 6) else 32

def setSteps (n : Nat) : Nat := if n = 0 then 2 else 4 * n + 3

def setWordOffset (n k : Nat) : Nat :=
  if k = 0 then 0 else if n = 0 then 24 else if k = 1 then 4
  else if k < 4 * n + 2 then 8 + 4 * ((k - 2) % 4) else 24

inductive MovePath where
  | empty | same | forward | backward
  deriving DecidableEq, Repr

def moveSteps (path : MovePath) (n : Nat) : Nat :=
  match path with
  | .empty => 2
  | .same => 4
  | .forward => 6 * n + 6
  | .backward => 6 * n + 7

def moveWordOffset (path : MovePath) (n k : Nat) : Nat :=
  match path with
  | .empty => if k = 0 then 0 else 48
  | .same => if k < 3 then 4 * k else 48
  | .forward =>
    if k < 4 then 4 * k else if k = 4 then 52
    else if k < 6 * n + 5 then 56 + 4 * ((k - 5) % 6) else 80
  | .backward =>
    if k < 6 then 4 * k
    else if k < 6 * n + 6 then 24 + 4 * ((k - 6) % 6) else 48

/-- The native offset schedule includes the actual return landing at the
first state after RET; treating it as another RET-PC would be incorrect. -/
def nativeOffset (base returnPC : BitVec 64) (steps : Nat) (wordOffset : Nat → Nat)
    (k : Nat) : BitVec 64 :=
  if k = steps then returnPC - base else BitVec.ofNat 64 (wordOffset k)

theorem return_landing (base returnPC : BitVec 64) (steps : Nat) (offset : Nat → Nat) :
    base + nativeOffset base returnPC steps offset steps = returnPC := by
  simp only [nativeOffset, ite_true]
  bv_omega

theorem counter_pred (remaining : BitVec 64) (positive : 0 < remaining.toNat) :
    (remaining - 1#64).toNat = remaining.toNat - 1 := by
  apply BitVec.toNat_sub_of_le
  simp only [BitVec.le_def, BitVec.toNat_ofNat]
  omega

theorem counter_decreases (remaining : BitVec 64) (positive : 0 < remaining.toNat) :
    (remaining - 1#64).toNat < remaining.toNat := by
  rw [counter_pred remaining positive]
  omega

/-- A modular cursor may be one past the valid object, since only its
predecessor is dereferenced in the backward loop. -/
theorem end_cursor_pred (base : BitVec 64) (r : Nat) (positive : 0 < r) :
    base + BitVec.ofNat 64 r - 1#64 = base + BitVec.ofNat 64 (r - 1) := by
  have rsplit : r = (r - 1) + 1 := by omega
  have castSplit : BitVec.ofNat 64 r = BitVec.ofNat 64 (r - 1) + 1#64 := by
    calc
      BitVec.ofNat 64 r = BitVec.ofNat 64 ((r - 1) + 1) := congrArg (BitVec.ofNat 64) rsplit
      _ = BitVec.ofNat 64 (r - 1) + 1#64 := BitVec.ofNat_add (r - 1) 1
  rw [castSplit]
  bv_omega

theorem copy_loop_offset (n i j : Nat) (room : i < n) (slot : j < 6) :
    copyWordOffset n (2 + 6 * i + j) = 8 + 4 * j := by
  have nz : n ≠ 0 := by omega
  have bound : 2 + 6 * i + j < 6 * n + 2 := by omega
  have index : 2 + 6 * i + j - 2 = 6 * i + j := by omega
  have rem : (6 * i + j) % 6 = j := by omega
  simp only [copyWordOffset, ite_eq_right (by omega : 2 + 6 * i + j ≠ 0), ite_eq_right nz,
    ite_eq_right (by omega : 2 + 6 * i + j ≠ 1), ite_eq_left bound, index, rem]

theorem copy_exit_offset (n : Nat) (positive : 0 < n) :
    copyWordOffset n (6 * n + 2) = 32 := by
  simp [copyWordOffset, show n ≠ 0 by omega, show 6 * n + 2 ≠ 1 by omega]

theorem copy_backedge_offset (n i : Nat) (again : i + 1 < n) :
    copyWordOffset n (2 + 6 * i + 5 + 1) = 8 := by
  have index : 2 + 6 * i + 5 + 1 = 2 + 6 * (i + 1) + 0 := by omega
  rw [index, copy_loop_offset n (i + 1) 0 again (by decide)]

theorem copy_last_branch_exit (n i : Nat) (last : i + 1 = n) (positive : 0 < n) :
    copyWordOffset n (2 + 6 * i + 5 + 1) = 32 := by
  have index : 2 + 6 * i + 5 + 1 = 6 * n + 2 := by omega
  rw [index, copy_exit_offset n positive]

theorem set_loop_offset (n i j : Nat) (room : i < n) (slot : j < 4) :
    setWordOffset n (2 + 4 * i + j) = 8 + 4 * j := by
  have nz : n ≠ 0 := by omega
  have bound : 2 + 4 * i + j < 4 * n + 2 := by omega
  have index : 2 + 4 * i + j - 2 = 4 * i + j := by omega
  have rem : (4 * i + j) % 4 = j := by omega
  simp only [setWordOffset, ite_eq_right (by omega : 2 + 4 * i + j ≠ 0), ite_eq_right nz,
    ite_eq_right (by omega : 2 + 4 * i + j ≠ 1), ite_eq_left bound, index, rem]

theorem copy_offset_aligned (n k : Nat) : copyWordOffset n k % 4 = 0 := by
  unfold copyWordOffset
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> omega

theorem set_offset_aligned (n k : Nat) : setWordOffset n k % 4 = 0 := by
  unfold setWordOffset
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> omega

theorem move_bound (path : MovePath) (n : Nat) : moveSteps path n ≤ 6 * n + 7 := by
  cases path <;> simp only [moveSteps] <;> omega

#print axioms return_landing
#print axioms counter_pred
#print axioms counter_decreases
#print axioms end_cursor_pred
#print axioms copy_loop_offset
#print axioms copy_exit_offset
#print axioms copy_backedge_offset
#print axioms copy_last_branch_exit
#print axioms set_loop_offset
#print axioms copy_offset_aligned
#print axioms set_offset_aligned
#print axioms move_bound

end ArmCertLoop.Schedule
