import Bridge.BvField
open BitVec
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to CryptoBridge.LogShiftDecodeLNSym.
namespace CryptoBridge.LogShift


/-- The logShift instruction word built from its fields. -/
def logShiftWord (sf : BitVec 1) (opc : BitVec 2) (shift : BitVec 2) (N : BitVec 1) (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) : BitVec 32 :=
  sf ++ opc ++ 10#5 ++ shift ++ N ++ Rm ++ imm6 ++ Rn ++ Rd

end CryptoBridge.LogShift

