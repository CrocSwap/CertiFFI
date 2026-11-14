import Bridge.BvField
open BitVec
namespace NativeEntryBodyDispatch.Cbz
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
/- Encoding candidate, checked against the ACTUAL outer dispatch theorem. -/
def word (f0 : BitVec 1) (f1 : BitVec 6) (f2 : BitVec 1) (imm19 : BitVec 19) (Rt : BitVec 5) : BitVec 32 := f0 ++ f1 ++ f2 ++ imm19 ++ Rt
/- The selected class word: constant fields fixed by the class. -/
def selected (Rt : BitVec 5) (imm19 : BitVec 19) : BitVec 32 := word 1#1 26#6 0#1 imm19 Rt
end NativeEntryBodyDispatch.Cbz
