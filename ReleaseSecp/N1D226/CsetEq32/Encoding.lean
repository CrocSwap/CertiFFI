import Bridge.BvField
open BitVec
namespace N1D226.CsetEq32.Encoding
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
def word (f0 : BitVec 27) (Rd : BitVec 5) : BitVec 32 := f0 ++ Rd
def selected (Rd : BitVec 5) : BitVec 32 := word 13957311#27 Rd
theorem selected_request : selected 0#5 = 446633952#32 := by decide
#print axioms selected_request
end N1D226.CsetEq32.Encoding
