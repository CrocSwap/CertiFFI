import Bridge.BvField
open BitVec
namespace N1D226.CmpShiftZero64.Encoding
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
def word (f0 : BitVec 16) (imm6 : BitVec 6) (Rn : BitVec 5) (f3 : BitVec 5) : BitVec 32 := f0 ++ imm6 ++ Rn ++ f3
def selected (Rn : BitVec 5) (imm6 : BitVec 6) : BitVec 32 := word 60191#16 imm6 Rn 31#5
theorem selected_request : selected 7#5 0#6 = 3944677631#32 := by decide
#print axioms selected_request
end N1D226.CmpShiftZero64.Encoding
