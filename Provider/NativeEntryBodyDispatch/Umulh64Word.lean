import Bridge.BvField
open BitVec
namespace NativeEntryBodyDispatch.Umulh64
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
/- Encoding candidate, checked against the ACTUAL outer dispatch theorem. -/
def word (f0 : BitVec 8) (f1 : BitVec 1) (f2 : BitVec 2) (Rm : BitVec 5) (f4 : BitVec 1) (f5 : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) : BitVec 32 := f0 ++ f1 ++ f2 ++ Rm ++ f4 ++ f5 ++ Rn ++ Rd
/- The selected class word: constant fields fixed by the class. -/
def selected (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) : BitVec 32 := word 155#8 1#1 2#2 Rm 0#1 31#5 Rn Rd
end NativeEntryBodyDispatch.Umulh64
