-- LNSym-free: Sail-side content only; the LNSym ArmInst decode theorem moved to CryptoMem.LdstPostDecodeLNSym.
open BitVec
namespace CryptoMem.LdstPost

/-- The ldstPost instruction word built from its fields. -/
def ldstPostWord (size : BitVec 2) (opc : BitVec 2) (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) : BitVec 32 :=
  size ++ 7#3 ++ 0#1 ++ 0#2 ++ opc ++ 0#1 ++ imm9 ++ 1#2 ++ Rn ++ Rt


end CryptoMem.LdstPost
