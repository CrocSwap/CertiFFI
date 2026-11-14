import Bridge.BvField
open BitVec
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to Crypto.BlDecodeLNSym.
namespace Crypto.BlDec


/-- The bl instruction word built from its fields. -/
def blWord (imm26 : BitVec 26) : BitVec 32 :=
  1#1 ++ 5#5 ++ imm26

end Crypto.BlDec

