import Bridge.BvField
open BitVec
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to Crypto.BcondDecodeLNSym.
namespace Crypto.BcondDec


/-- The bcond instruction word built from its fields. -/
def bcondWord (imm19 : BitVec 19) (cond : BitVec 4) : BitVec 32 :=
  84#8 ++ imm19 ++ 0#1 ++ cond

end Crypto.BcondDec

