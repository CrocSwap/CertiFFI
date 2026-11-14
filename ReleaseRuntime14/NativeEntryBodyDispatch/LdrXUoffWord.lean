import Bridge.BvField
open BitVec
namespace NativeEntryBodyDispatch.LdrXUoff
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
/- Encoding candidate, checked against the ACTUAL outer dispatch theorem. -/
def word (f0 : BitVec 2) (f1 : BitVec 6) (f2 : BitVec 2) (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) : BitVec 32 := f0 ++ f1 ++ f2 ++ imm12 ++ Rn ++ Rt
/- The selected class word: constant fields fixed by the class. -/
def selected (Rt : BitVec 5) (Rn : BitVec 5) (imm12 : BitVec 12) : BitVec 32 := word 3#2 57#6 1#2 imm12 Rn Rt
end NativeEntryBodyDispatch.LdrXUoff
