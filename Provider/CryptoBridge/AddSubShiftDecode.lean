import Bridge.BvField
open BitVec
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to CryptoBridge.AddSubShiftDecodeLNSym.
namespace CryptoBridge.AddSubShift


/-- The addSubShift instruction word built from its fields. -/
def addSubShiftWord (sf : BitVec 1) (op : BitVec 1) (S : BitVec 1) (shift : BitVec 2) (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) : BitVec 32 :=
  sf ++ op ++ S ++ 11#5 ++ shift ++ 0#1 ++ Rm ++ imm6 ++ Rn ++ Rd

end CryptoBridge.AddSubShift

