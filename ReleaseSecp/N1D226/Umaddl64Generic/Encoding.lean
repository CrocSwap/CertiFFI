import Bridge.BvField
open BitVec
namespace N1D226.Umaddl64Generic.Encoding
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
def word (f0 : BitVec 11) (Rm : BitVec 5) (f2 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) : BitVec 32 := f0 ++ Rm ++ f2 ++ Rn ++ Rd
def selected (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) : BitVec 32 := word 1245#11 Rm 31#6 Rn Rd
theorem selected_request : selected 2#5 10#5 10#5 = 2611641666#32 := by decide
#print axioms selected_request
end N1D226.Umaddl64Generic.Encoding
