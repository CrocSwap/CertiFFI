import Bridge.BvField
open BitVec
namespace NativeEntryBodyDispatch.OrrMov64
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
/- Encoding candidate, checked against the ACTUAL outer dispatch theorem. -/
def word (f0 : BitVec 1) (f1 : BitVec 2) (f2 : BitVec 5) (f3 : BitVec 2) (f4 : BitVec 1) (Rm : BitVec 5) (imm6 : BitVec 6) (f7 : BitVec 5) (Rd : BitVec 5) : BitVec 32 := f0 ++ f1 ++ f2 ++ f3 ++ f4 ++ Rm ++ imm6 ++ f7 ++ Rd
/- The selected class word: constant fields fixed by the class. -/
def selected (Rd : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) : BitVec 32 := word 1#1 1#2 10#5 0#2 0#1 Rm imm6 31#5 Rd
end NativeEntryBodyDispatch.OrrMov64
