import Bridge.BvField
open BitVec
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to Bridge.AdcDecodeLNSym.


/-- The ADC/ADCS/SBC/SBCS instruction word built from its fields. -/
def adcWord (sf op S : BitVec 1) (Rm Rn Rd : BitVec 5) : BitVec 32 :=
  sf ++ op ++ S ++ 208#8 ++ Rm ++ 0#6 ++ Rn ++ Rd


