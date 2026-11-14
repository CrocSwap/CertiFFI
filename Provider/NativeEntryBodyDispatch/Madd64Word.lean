import Bridge.BvField
open BitVec
namespace NativeEntryBodyDispatch.Madd64
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
/- Encoding candidate, checked against the ACTUAL outer dispatch theorem. -/
def word (f0 : BitVec 1) (f1 : BitVec 10) (Rm : BitVec 5) (f3 : BitVec 1) (f4 : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) : BitVec 32 := f0 ++ f1 ++ Rm ++ f3 ++ f4 ++ Rn ++ Rd
/- The selected class word: constant fields fixed by the class. -/
def selected (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) : BitVec 32 := word 1#1 216#10 Rm 0#1 31#5 Rn Rd
end NativeEntryBodyDispatch.Madd64
