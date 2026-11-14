import Bridge.BvField
open BitVec
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to CryptoBridge.CondSelDecodeLNSym.
namespace CryptoBridge.CondSel


/-- The condSel instruction word built from its fields. -/
def condSelWord (sf : BitVec 1) (op : BitVec 1) (S : BitVec 1) (Rm : BitVec 5) (cond : BitVec 4) (op2 : BitVec 2) (Rn : BitVec 5) (Rd : BitVec 5) : BitVec 32 :=
  sf ++ op ++ S ++ 212#8 ++ Rm ++ cond ++ op2 ++ Rn ++ Rd

end CryptoBridge.CondSel

