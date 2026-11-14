-- CT0 v2.1 run-to-return (addendum 7, RT1-RT4; form): the shared code-range predicate. Dependency-free
-- (core BitVec only) so every root tree can compile it into its own ob. pins this definition by exact --defpp.
set_option autoImplicit false
namespace CT0Ret

/-- `pc` lies in one of the half-open code intervals [base + lo, base + hi), offsets entry-relative (ELF symbol extents). -/
def InCode (base pc : BitVec 64) (rs : List (Nat × Nat)) : Prop :=
  ∃ r ∈ rs, base + BitVec.ofNat 64 r.1 ≤ pc ∧ pc < base + BitVec.ofNat 64 r.2

end CT0Ret
