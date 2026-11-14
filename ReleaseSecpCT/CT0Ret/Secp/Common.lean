-- CT0 v2.1 run-to-return (addendum 7) for secp: generic range lemma over CT0Ret.InCode.
import CT0Ret
set_option autoImplicit false
namespace CT0Ret.Secp

/-- A code offset inside one of two half-open intervals is `InCode` at `base + offset`, provided base and the interval
    ends are below 2^54 (no 64-bit wrap). -/
theorem inCode_two (base : BitVec 64) (hb : base.toNat < 2 ^ 54) (a b c d w : Nat) (hb' : b < 2 ^ 54) (hd : d < 2 ^ 54)
    (h : (a ≤ w ∧ w < b) ∨ (c ≤ w ∧ w < d)) :
    CT0Ret.InCode base (base + BitVec.ofNat 64 w) [(a, b), (c, d)] := by
  have key : ∀ lo hi, hi < 2 ^ 54 → lo ≤ w → w < hi →
      base + BitVec.ofNat 64 lo ≤ base + BitVec.ofNat 64 w ∧ base + BitVec.ofNat 64 w < base + BitVec.ofNat 64 hi := by
    intro lo hi hh h1 h2
    constructor
    · rw [BitVec.le_def]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · rw [BitVec.lt_def]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rcases h with h | h
  · exact ⟨(a, b), by simp, key a b hb' h.1 h.2⟩
  · exact ⟨(c, d), by simp, key c d hd h.1 h.2⟩

end CT0Ret.Secp
#print axioms CT0Ret.Secp.inCode_two
