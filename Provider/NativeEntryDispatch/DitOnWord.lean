import ArmFull
import Bridge.BvField
open BitVec
namespace NativeEntryDispatch.DitOn
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
/- Encoding candidate is checked against the ACTUAL outer dispatch theorem. -/
def word  : BitVec 32 := BitVec.append (111680010#27) (31#5)
end NativeEntryDispatch.DitOn
