import Bridge.BvField
open BitVec
namespace N1D226.AdcZeroRn64Generic.Encoding
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
def word (f0 : BitVec 11) (Rm : BitVec 5) (f2 : BitVec 11) (Rd : BitVec 5) : BitVec 32 := f0 ++ Rm ++ f2 ++ Rd
def selected (Rd : BitVec 5) (Rm : BitVec 5) : BitVec 32 := word 1232#11 Rm 31#11 Rd
theorem selected_request : selected 4#5 4#5 = 2583954404#32 := by decide
#print axioms selected_request
end N1D226.AdcZeroRn64Generic.Encoding
