import Bridge.BvField
open BitVec
namespace NativeEntryBodyDispatch.Adcs64
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
/- Encoding candidate, checked against the ACTUAL outer dispatch theorem. -/
def word (f0 : BitVec 1) (f1 : BitVec 1) (f2 : BitVec 1) (f3 : BitVec 8) (Rm : BitVec 5) (f5 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) : BitVec 32 := f0 ++ f1 ++ f2 ++ f3 ++ Rm ++ f5 ++ Rn ++ Rd
/- The selected class word: constant fields fixed by the class. -/
def selected (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) : BitVec 32 := word 1#1 0#1 1#1 208#8 Rm 0#6 Rn Rd
end NativeEntryBodyDispatch.Adcs64
