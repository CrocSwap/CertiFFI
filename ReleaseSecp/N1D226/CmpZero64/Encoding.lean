import Bridge.BvField
open BitVec
namespace N1D226.CmpZero64.Encoding
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
def word (f0 : BitVec 10) (imm12 : BitVec 12) (Rn : BitVec 5) (f3 : BitVec 5) : BitVec 32 := f0 ++ imm12 ++ Rn ++ f3
def selected (Rn : BitVec 5) (imm12 : BitVec 12) : BitVec 32 := word 964#10 imm12 Rn 31#5
theorem selected_request : selected 0#5 0#12 = 4043309087#32 := by decide
#print axioms selected_request
end N1D226.CmpZero64.Encoding
