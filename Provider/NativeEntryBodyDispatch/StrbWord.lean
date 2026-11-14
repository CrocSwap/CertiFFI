import Bridge.BvField
open BitVec
namespace NativeEntryBodyDispatch.Strb
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
/- Encoding candidate, checked against the ACTUAL outer dispatch theorem. -/
def word (f0 : BitVec 2) (f1 : BitVec 6) (f2 : BitVec 2) (f3 : BitVec 1) (imm9 : BitVec 9) (f5 : BitVec 2) (Rn : BitVec 5) (Rt : BitVec 5) : BitVec 32 := f0 ++ f1 ++ f2 ++ f3 ++ imm9 ++ f5 ++ Rn ++ Rt
/- The selected class word: constant fields fixed by the class. -/
def selected (Rt : BitVec 5) (Rn : BitVec 5) (imm9 : BitVec 9) : BitVec 32 := word 0#2 56#6 0#2 0#1 imm9 1#2 Rn Rt
end NativeEntryBodyDispatch.Strb
