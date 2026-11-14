import Bridge.BvField
open BitVec
namespace NativeEntryBodyDispatch.Csel3
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
/- Encoding candidate, checked against the ACTUAL outer dispatch theorem. -/
def word (f0 : BitVec 1) (f1 : BitVec 1) (f2 : BitVec 9) (f3 : BitVec 5) (f4 : BitVec 4) (f5 : BitVec 1) (f6 : BitVec 1) (Rn : BitVec 5) (Rd : BitVec 5) : BitVec 32 := f0 ++ f1 ++ f2 ++ f3 ++ f4 ++ f5 ++ f6 ++ Rn ++ Rd
/- The selected class word: constant fields fixed by the class. -/
def selected (Rd : BitVec 5) (Rn : BitVec 5) : BitVec 32 := word 1#1 0#1 212#9 31#5 3#4 0#1 0#1 Rn Rd
end NativeEntryBodyDispatch.Csel3
