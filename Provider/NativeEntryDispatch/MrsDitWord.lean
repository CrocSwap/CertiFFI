import ArmFull
import Bridge.BvField
open BitVec
namespace NativeEntryDispatch.MrsDit
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
/- Encoding candidate is checked against the ACTUAL outer dispatch theorem. -/
def word (Rt : BitVec 5) : BitVec 32 := BitVec.append (111794709#27) (Rt)
end NativeEntryDispatch.MrsDit
