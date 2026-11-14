import Bridge.BvField
open BitVec
namespace NativeEntryBodyDispatch.Tbnz32
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
/- Encoding candidate, checked against the ACTUAL outer dispatch theorem. -/
def word (f0 : BitVec 1) (f1 : BitVec 6) (f2 : BitVec 1) (f3 : BitVec 5) (imm14 : BitVec 14) (Rt : BitVec 5) : BitVec 32 := f0 ++ f1 ++ f2 ++ f3 ++ imm14 ++ Rt
/- The selected class word: constant fields fixed by the class. -/
def selected (Rt : BitVec 5) (imm14 : BitVec 14) : BitVec 32 := word 0#1 27#6 1#1 0#5 imm14 Rt
end NativeEntryBodyDispatch.Tbnz32
