import Bridge.BvField
open BitVec
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to CryptoBridge.LogImmDecodeLNSym.
namespace CryptoBridge.LogImm


/-- The logImm instruction word built from its fields. -/
def logImmWord (sf : BitVec 1) (opc : BitVec 2) (N : BitVec 1) (immr : BitVec 6) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) : BitVec 32 :=
  sf ++ opc ++ 36#6 ++ N ++ immr ++ imms ++ Rn ++ Rd

end CryptoBridge.LogImm

