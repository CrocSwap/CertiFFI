-- CT0 v2.1 run-to-return for route 7 (addendum 7): a word PC of a routine [lo, lo+4·nw) is InCode.
import CT0Ret
set_option autoImplicit false
namespace CT0Ret.Route7

theorem inCode_word (base : BitVec 64) (hb : base.toNat < 2 ^ 54) (lo nw j : Nat) (hj : j < nw)
    (hsm : lo + 4 * nw < 2 ^ 54) :
    CT0Ret.InCode base (base + BitVec.ofNat 64 (lo + 4 * j)) [(lo, lo + 4 * nw)] := by
  refine ⟨(lo, lo + 4 * nw), List.mem_singleton_self _, ?_, ?_⟩
  · simp only [BitVec.le_def, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]; omega
  · simp only [BitVec.lt_def, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]; omega

end CT0Ret.Route7
#print axioms CT0Ret.Route7.inCode_word
