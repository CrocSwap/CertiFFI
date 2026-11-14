import Bridge.BvField
open BitVec
namespace N1D226.Extr64Generic.Encoding
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
def word (f0 : BitVec 11) (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) : BitVec 32 := f0 ++ Rm ++ imms ++ Rn ++ Rd
def selected (Rd : BitVec 5) (Rn : BitVec 5) (imms : BitVec 6) (Rm : BitVec 5) : BitVec 32 := word 1182#11 Rm imms Rn Rd
theorem selected_request : selected 5#5 5#5 63#6 4#5 = 2479160485#32 := by decide
#print axioms selected_request
end N1D226.Extr64Generic.Encoding
