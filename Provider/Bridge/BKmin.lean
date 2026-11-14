import Bridge.PremiseFree
import BK3.Halted
import BK3.EDSCRread
import BK3.EDSCRwritePipeAdv
import BK3.ThisInstrAddr64
import BK3.ThisInstrLength
import BK3.PMUEventInstSpec
import BK3.PMUEventInstRetired
import BK3.SSAdvance
import BK3.CheckResetCatch
import BKv.spePre
import BKv.spePost
import BKv.emu
import BKv.speCycle
import BKv.endCycle
import BK.setdet
import BK.defcond
import BK.eret
import BKv.usingA32
namespace ArmBridge.BKmin
#premise_min ArmBridge.BKmin.Halted from BK3_Halted.complete
#premise_min ArmBridge.BKmin.EDSCRread from BK3_EDSCRread.complete
#premise_min ArmBridge.BKmin.EDSCRwritePipeAdv from BK3_EDSCRwritePipeAdv.complete
#premise_min ArmBridge.BKmin.ThisInstrAddr64 from BK3_ThisInstrAddr64.complete
#premise_min ArmBridge.BKmin.ThisInstrLength from BK3_ThisInstrLength.complete
#premise_min ArmBridge.BKmin.PMUEventInstSpec from BK3_PMUEventInstSpec.complete
#premise_min ArmBridge.BKmin.PMUEventInstRetired from BK3_PMUEventInstRetired.complete
#premise_min ArmBridge.BKmin.SSAdvance from BK3_SSAdvance.complete
#premise_min ArmBridge.BKmin.CheckResetCatch from BK3_CheckResetCatch.complete
#premise_min ArmBridge.BKmin.spePre from ArmBridge.BKv.spePre_complete
#premise_min ArmBridge.BKmin.spePost from ArmBridge.BKv.spePost_complete
#premise_min ArmBridge.BKmin.emu from ArmBridge.BKv.emu_complete
#premise_min ArmBridge.BKmin.speCycle from ArmBridge.BKv.speCycle_complete
#premise_min ArmBridge.BKmin.endCycle from ArmBridge.BKv.endCycle_complete
#premise_min ArmBridge.BKmin.setdet from ArmBridge.BK.setdet_complete
#premise_min ArmBridge.BKmin.defcond from ArmBridge.BK.defcond_complete
#premise_min ArmBridge.BKmin.eret from ArmBridge.BK.eret_complete
#premise_min ArmBridge.BKmin.usingA32 from ArmBridge.BKv.usingA32_complete
end ArmBridge.BKmin
