import Bridge.BvField
open BitVec
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to Crypto.CbzDecodeLNSym.
namespace Crypto.CbzDec


/-- The cbz instruction word built from its fields. -/
def cbzWord (sf : BitVec 1) (op : BitVec 1) (imm19 : BitVec 19) (Rt : BitVec 5) : BitVec 32 :=
  sf ++ 26#6 ++ op ++ imm19 ++ Rt

end Crypto.CbzDec

