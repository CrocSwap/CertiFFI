-- LNSym-free: Sail-side content only; the LNSym ArmInst decode theorem moved to CryptoMem.LdstPairDecodeLNSym.
open BitVec
namespace CryptoMem.LdstPair

/-- The ldstPairOff instruction word built from its fields. -/
def ldstPairOffWord (opc : BitVec 2) (L : BitVec 1) (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) : BitVec 32 :=
  opc ++ 5#3 ++ 0#1 ++ 2#3 ++ L ++ imm7 ++ Rt2 ++ Rn ++ Rt



end CryptoMem.LdstPair
