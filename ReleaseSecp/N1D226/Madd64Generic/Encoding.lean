import Bridge.BvField
open BitVec
namespace N1D226.Madd64Generic.Encoding
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
def word (f0 : BitVec 11) (Rm : BitVec 5) (f2 : BitVec 1) (Ra : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) : BitVec 32 := f0 ++ Rm ++ f2 ++ Ra ++ Rn ++ Rd
def selected (Rd : BitVec 5) (Rn : BitVec 5) (Ra : BitVec 5) (Rm : BitVec 5) : BitVec 32 := word 1240#11 Rm 0#1 Ra Rn Rd
theorem selected_request : selected 15#5 16#5 15#5 2#5 = 2600615439#32 := by decide
#print axioms selected_request
end N1D226.Madd64Generic.Encoding
