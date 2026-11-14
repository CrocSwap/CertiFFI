import ArmCertLoop.Chain

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

namespace ArmCertLoop.Bytes

/-! Exact-byte mathematics used inside loop proofs. A ByteView is a view of
RAM, not machine semantics. Instruction adapters derive SingleWrite from
their actual Sail runs. src/dst denote the physical address of each logical
buffer byte; layout/ordering lemmas discharge all freshness conditions. -/

abbrev ByteView := Nat → Option (BitVec 8)

structure SingleWrite (before after : ByteView) (pa : Nat) (byte : BitVec 8) : Prop where
  written : after pa = some byte
  frame : ∀ q, q ≠ pa → after q = before q

structure CopyPrefix (src dst : Nat → Nat) (initial current : ByteView) (n i : Nat) : Prop where
  bound : i ≤ n
  copied : ∀ j, j < i → current (dst j) = initial (src j)
  unread : ∀ j, i ≤ j → j < n → current (src j) = initial (src j)
  frame : ∀ q, (¬ ∃ j, j < i ∧ dst j = q) → current q = initial q

theorem copyPrefix_zero (src dst : Nat → Nat) (initial : ByteView) (n : Nat) :
    CopyPrefix src dst initial initial n 0 := by
  constructor
  · omega
  · intro j h; omega
  · intros; rfl
  · intros; rfl

/-- Advance one exact byte from the original source snapshot, preserving all
unread source bytes. Forward-overlap and disjoint copying use the same lemma. -/
theorem copyPrefix_succ {src dst : Nat → Nat} {initial before after : ByteView}
    {n i : Nat} {byte : BitVec 8}
    (inv : CopyPrefix src dst initial before n i) (room : i < n)
    (value : before (src i) = some byte)
    (write : SingleWrite before after (dst i) byte)
    (oldDst : ∀ j, j < i → dst j ≠ dst i)
    (futureSrc : ∀ j, i < j → j < n → src j ≠ dst i) :
    CopyPrefix src dst initial after n (i + 1) := by
  have original : initial (src i) = some byte := (inv.unread i (by omega) room).symm.trans value
  constructor
  · omega
  · intro j hj
    by_cases same : j = i
    · subst j; exact write.written.trans original.symm
    · have prior : j < i := by omega
      exact (write.frame (dst j) (oldDst j prior)).trans (inv.copied j prior)
  · intro j hj hn
    exact (write.frame (src j) (futureSrc j (by omega) hn)).trans (inv.unread j (by omega) hn)
  · intro q outside
    have fresh : q ≠ dst i := by
      intro equal
      exact outside ⟨i, by omega, equal.symm⟩
    have oldOutside : ¬ ∃ j, j < i ∧ dst j = q := by
      rintro ⟨j, hj, he⟩
      exact outside ⟨j, by omega, he⟩
    exact (write.frame q fresh).trans (inv.frame q oldOutside)

structure CopySuffix (src dst : Nat → Nat) (initial current : ByteView) (n r : Nat) : Prop where
  bound : r ≤ n
  copied : ∀ j, r ≤ j → j < n → current (dst j) = initial (src j)
  unread : ∀ j, j < r → current (src j) = initial (src j)
  frame : ∀ q, (¬ ∃ j, r ≤ j ∧ j < n ∧ dst j = q) → current q = initial q

theorem copySuffix_start (src dst : Nat → Nat) (initial : ByteView) (n : Nat) :
    CopySuffix src dst initial initial n n := by
  constructor
  · omega
  · intro j hj hn; omega
  · intros; rfl
  · intros; rfl

/-- Copy index r-1 before decreasing the suffix boundary. Source and
destination may overlap; only already-written/future-unread conflicts matter. -/
theorem copySuffix_pred {src dst : Nat → Nat} {initial before after : ByteView}
    {n r : Nat} {byte : BitVec 8}
    (inv : CopySuffix src dst initial before n r) (positive : 0 < r)
    (value : before (src (r - 1)) = some byte)
    (write : SingleWrite before after (dst (r - 1)) byte)
    (oldDst : ∀ j, r ≤ j → j < n → dst j ≠ dst (r - 1))
    (futureSrc : ∀ j, j < r - 1 → src j ≠ dst (r - 1)) :
    CopySuffix src dst initial after n (r - 1) := by
  have bound := inv.bound
  have original : initial (src (r - 1)) = some byte :=
    (inv.unread (r - 1) (by omega)).symm.trans value
  constructor
  · omega
  · intro j hj hn
    by_cases same : j = r - 1
    · subst j; exact write.written.trans original.symm
    · have prior : r ≤ j := by omega
      exact (write.frame (dst j) (oldDst j prior hn)).trans (inv.copied j prior hn)
  · intro j hj
    exact (write.frame (src j) (futureSrc j hj)).trans (inv.unread j (by omega))
  · intro q outside
    have fresh : q ≠ dst (r - 1) := by
      intro equal
      exact outside ⟨r - 1, by omega, by omega, equal.symm⟩
    have oldOutside : ¬ ∃ j, r ≤ j ∧ j < n ∧ dst j = q := by
      rintro ⟨j, hj, hn, he⟩
      exact outside ⟨j, by omega, hn, he⟩
    exact (write.frame q fresh).trans (inv.frame q oldOutside)

structure FillPrefix (dst : Nat → Nat) (initial current : ByteView) (byte : BitVec 8)
    (n i : Nat) : Prop where
  bound : i ≤ n
  filled : ∀ j, j < i → current (dst j) = some byte
  frame : ∀ q, (¬ ∃ j, j < i ∧ dst j = q) → current q = initial q

theorem fillPrefix_zero (dst : Nat → Nat) (initial : ByteView) (byte : BitVec 8) (n : Nat) :
    FillPrefix dst initial initial byte n 0 := by
  constructor
  · omega
  · intro j h; omega
  · intros; rfl

theorem fillPrefix_succ {dst : Nat → Nat} {initial before after : ByteView}
    {n i : Nat} {byte : BitVec 8}
    (inv : FillPrefix dst initial before byte n i) (room : i < n)
    (write : SingleWrite before after (dst i) byte)
    (oldDst : ∀ j, j < i → dst j ≠ dst i) :
    FillPrefix dst initial after byte n (i + 1) := by
  constructor
  · omega
  · intro j hj
    by_cases same : j = i
    · subst j; exact write.written
    · have prior : j < i := by omega
      exact (write.frame (dst j) (oldDst j prior)).trans (inv.filled j prior)
  · intro q outside
    have fresh : q ≠ dst i := by
      intro equal
      exact outside ⟨i, by omega, equal.symm⟩
    have oldOutside : ¬ ∃ j, j < i ∧ dst j = q := by
      rintro ⟨j, hj, he⟩
      exact outside ⟨j, by omega, he⟩
    exact (write.frame q fresh).trans (inv.frame q oldOutside)

/-- Forward copy at i cannot clobber an unread later source index. -/
theorem forward_address_ne {d s i j : Nat} (direction : d ≤ s) (future : i < j) :
    s + j ≠ d + i := by omega

/-- Backward copy at i cannot clobber an unread earlier source index. -/
theorem backward_address_ne {d s i j : Nat} (direction : s < d) (future : j < i) :
    s + j ≠ d + i := by omega

/-- Restrict mapping injectivity to the accessed union, rather than all VAs. -/
theorem mapped_ne {map : Nat → Nat} {domain : Nat → Prop} {a b : Nat}
    (injective : ∀ x, domain x → ∀ y, domain y → map x = map y → x = y)
    (ha : domain a) (hb : domain b) (different : a ≠ b) : map a ≠ map b := by
  intro equal
  exact different (injective a ha b hb equal)

#print axioms copyPrefix_zero
#print axioms copyPrefix_succ
#print axioms copySuffix_start
#print axioms copySuffix_pred
#print axioms fillPrefix_zero
#print axioms fillPrefix_succ
#print axioms forward_address_ne
#print axioms backward_address_ne
#print axioms mapped_ne

end ArmCertLoop.Bytes
