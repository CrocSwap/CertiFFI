import Bridge.BvField
open BitVec
namespace N1D226.AddsShift64Generic.Encoding
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
def word (f0 : BitVec 11) (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) : BitVec 32 := f0 ++ Rm ++ imm6 ++ Rn ++ Rd
def selected (Rd : BitVec 5) (Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) : BitVec 32 := word 1368#11 Rm imm6 Rn Rd
theorem selected_request : selected 4#5 4#5 32#6 15#5 = 2869919876#32 := by decide
#print axioms selected_request
end N1D226.AddsShift64Generic.Encoding
