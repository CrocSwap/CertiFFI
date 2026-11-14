-- BR8 L2: BcondAction base (MTE2-free complete_pa), shared by Obs/Extra.
import TranslateSpan.BrToRwMTE
import NativeEntryBodyBranch.Bcond
import TranslateSpan.BranchMTE2
import DropUnusedPremise
-- Actual B.cond action with no MTE2 premise.
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
namespace ReleaseProfile.BcondAction
open ArmBridge.Draft ArmBridge.CruxGenBr Crypto.CruxBrObl Crypto.BcondDec Crypto.BcondCore
attribute [local instance 10] Classical.propDecidable
set_option autoImplicit false
set_option maxRecDepth 512
set_option Elab.async false

#check "CURRENT_DECL complete_pa"
drop_unused_premise complete_pa from BR_BCondH.complete_pa named "hFeature_MTE2"
end ReleaseProfile.BcondAction
