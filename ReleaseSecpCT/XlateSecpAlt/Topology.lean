import XlateSecpAlt.Raw
import PipeLean_D234_SecpNeg_c10.EntryBinding
import XlateSecp.Topology

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# Secp topology check at the source-built entry (Translate, next train; speed mode)

`SecpRawDeployment.addresses` reads the entry only through its GPRs; the source-built entry's GPRs are the
world data's (`sourceRegs` keeps `data.gpr`). So the check reduces, without unfolding the register file, to
a closed `decide` over the world tables and the card's plan.
-/

namespace XlateSecpAlt.Topology

open Sail ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ArmBridge.Draft
open ArmBridge.CruxGenGuarded NativeAccess ArmCertValue ArmCertPipe
open ReleaseProfile.MachineSource ReleaseProfile.GB10 TranslateSpan TranslateSpan.SecpRawDeployment

theorem entry_gpr (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (c : XlateSecp.World.Card) (pcount : BitVec 88) : (XlateSecpAlt.World.entry sem rho caller c pcount).regs.gpr = (XlateSecp.World.data c).gpr := rfl

end XlateSecpAlt.Topology

