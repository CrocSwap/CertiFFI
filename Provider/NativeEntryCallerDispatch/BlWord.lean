import ArmFull
import Bridge.BvField
namespace NativeEntryCallerDispatch.Bl
set_option autoImplicit false
def word (imm26 : BitVec 26) : BitVec 32 := BitVec.append (37#6) imm26
end NativeEntryCallerDispatch.Bl
