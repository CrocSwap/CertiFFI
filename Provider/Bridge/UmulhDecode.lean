import Bridge.BvField
open BitVec
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to Bridge.UmulhDecodeLNSym.


/-- The umulh instruction word built from its fields. -/
def umulhWord (U : BitVec 1) (Rm : BitVec 5) (Ra : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) : BitVec 32 :=
  1#1 ++ 0#2 ++ 27#5 ++ U ++ 2#2 ++ Rm ++ 0#1 ++ Ra ++ Rn ++ Rd


