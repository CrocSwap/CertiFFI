import Bridge.BvField
open BitVec
namespace NativeEntryBodyDispatch.B
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
/- Encoding candidate, checked against the ACTUAL outer dispatch theorem. -/
def word (f0 : BitVec 1) (f1 : BitVec 5) (imm26 : BitVec 26) : BitVec 32 := f0 ++ f1 ++ imm26
/- The selected class word: constant fields fixed by the class. -/
def selected (imm26 : BitVec 26) : BitVec 32 := word 0#1 5#5 imm26
end NativeEntryBodyDispatch.B
