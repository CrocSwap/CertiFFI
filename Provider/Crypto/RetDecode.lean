import Bridge.BvField
open BitVec
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to Crypto.RetDecodeLNSym.
namespace Crypto.RetDec


/-- The ret instruction word built from its fields. -/
def retWord (Rn : BitVec 5) : BitVec 32 :=
  107#7 ++ 2#4 ++ 31#5 ++ 0#6 ++ Rn ++ 0#5

end Crypto.RetDec

