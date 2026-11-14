import ArmFull
import Bridge.BvField
import NativeEntry.MsrDitDispatch
open BitVec
namespace NativeEntryDispatch.MsrDit
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
/- Encoding candidate is checked against the ACTUAL outer dispatch theorem. -/
def word (Rt : BitVec 5) : BitVec 32 := BitVec.append (111729173#27) (Rt)
theorem effect_word : ∀ Rt : BitVec 5,
    word Rt = NativeEntry.MsrDit.Dispatch.word Rt := by decide +kernel
#print axioms effect_word
end NativeEntryDispatch.MsrDit
