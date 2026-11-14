import Bridge.BvField
open BitVec
namespace NativeEntryBodyDispatch.Bcond
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
/- Encoding candidate, checked against the ACTUAL outer dispatch theorem. -/
def word (f0 : BitVec 8) (imm19 : BitVec 19) (f2 : BitVec 1) (cond : BitVec 4) : BitVec 32 := f0 ++ imm19 ++ f2 ++ cond
/- The selected class word: constant fields fixed by the class. -/
def selected (cond : BitVec 4) (imm19 : BitVec 19) : BitVec 32 := word 84#8 imm19 0#1 cond
end NativeEntryBodyDispatch.Bcond
