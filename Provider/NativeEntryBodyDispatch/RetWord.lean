import Bridge.BvField
open BitVec
namespace NativeEntryBodyDispatch.Ret
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
/- Encoding candidate, checked against the ACTUAL outer dispatch theorem. -/
def word (f0 : BitVec 7) (f1 : BitVec 1) (f2 : BitVec 1) (f3 : BitVec 2) (f4 : BitVec 9) (f5 : BitVec 1) (f6 : BitVec 1) (Rn : BitVec 5) (f8 : BitVec 5) : BitVec 32 := f0 ++ f1 ++ f2 ++ f3 ++ f4 ++ f5 ++ f6 ++ Rn ++ f8
/- The selected class word: constant fields fixed by the class. -/
def selected (Rn : BitVec 5) : BitVec 32 := word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5
end NativeEntryBodyDispatch.Ret
