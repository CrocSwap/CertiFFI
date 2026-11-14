import Bridge.BvField
open BitVec
namespace NativeEntryBodyDispatch.AndsImm0_2
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
/- Encoding candidate, checked against the ACTUAL outer dispatch theorem. -/
def word (f0 : BitVec 1) (f1 : BitVec 2) (f2 : BitVec 6) (f3 : BitVec 1) (f4 : BitVec 6) (f5 : BitVec 6) (Rn : BitVec 5) (f7 : BitVec 5) : BitVec 32 := f0 ++ f1 ++ f2 ++ f3 ++ f4 ++ f5 ++ Rn ++ f7
/- The selected class word: constant fields fixed by the class. -/
def selected (Rn : BitVec 5) : BitVec 32 := word 1#1 3#2 36#6 1#1 0#6 2#6 Rn 31#5
end NativeEntryBodyDispatch.AndsImm0_2
