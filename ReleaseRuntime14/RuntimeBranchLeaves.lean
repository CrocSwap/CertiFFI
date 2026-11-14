import DropUnusedPremise
import NativeR14B.CbzPinsPrefix
import NativeR14B.TbnzPinsPrefix

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000

namespace ReleaseProfile.RuntimeBranchLeaves

#check "CURRENT_DECL cbz_prefix"
drop_unused_premise cbz_prefix from NativeR14B.CbzPinsPrefix_complete named "hFeature_MTE2"

#check "CURRENT_DECL tbnz_prefix"
drop_unused_premise tbnz_prefix from NativeR14B.TbnzPinsPrefix_complete named "hFeature_MTE2"

#print axioms cbz_prefix
#print axioms tbnz_prefix

end ReleaseProfile.RuntimeBranchLeaves
