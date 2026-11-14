import TagCheckFrames.Automation
import ArmCertWalk.NativeFetchPreservingEvents
import NativeAccess.Current
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open TagCheckFrames
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace TagCheckFrames
 theorem translation_preserves (va : BitVec 64) (acc : AccessDescriptor) (aligned : Bool) (size : Int) :
    Preserves (AArch64_TranslateAddress va acc aligned size) := by oracle_frame
#print axioms translation_preserves
end TagCheckFrames
