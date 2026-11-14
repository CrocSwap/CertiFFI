import Bridge.BvField
open BitVec
namespace NativeEntryBodyDispatch.Stp8
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
/- Encoding candidate, checked against the ACTUAL outer dispatch theorem. -/
def word (f0 : BitVec 2) (f1 : BitVec 7) (f2 : BitVec 1) (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) : BitVec 32 := f0 ++ f1 ++ f2 ++ imm7 ++ Rt2 ++ Rn ++ Rt
/- The selected class word: constant fields fixed by the class. -/
def selected (Rt : BitVec 5) (Rn : BitVec 5) (Rt2 : BitVec 5) (imm7 : BitVec 7) : BitVec 32 := word 2#2 82#7 0#1 imm7 Rt2 Rn Rt
end NativeEntryBodyDispatch.Stp8
