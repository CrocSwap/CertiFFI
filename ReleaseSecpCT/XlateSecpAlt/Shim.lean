import XlateSecpAlt.Queries
import XlateSecpAlt.LayoutAll
import SecpStaticsAlt
import DitShim243.Deployment
import DitShim243.SlotCheck
import XlateSecp.Shim

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# Secp shim-entry (scope B) generic leaves (Translate; speed mode)

The shim-extended plan (`DitShim243.Deployment.extend p start imm`) and its global address list read the entry only
through its GPRs and the constant save slot; restated over the GPR vector (`rfl`) so per-card checks are closed
decisions. The queries (route B) reuse `XlateSecpAlt.Queries` (XlateSecp.Queries.WorldSpec/XlateSecp.Queries.WorldRegs + `a124_tac`).
-/

namespace XlateSecpAlt.Shim

open Sail ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ArmBridge.Draft
open ArmBridge.CruxGenGuarded NativeAccess ArmCertValue ArmCertPipe
open ReleaseProfile.MachineSource ReleaseProfile.GB10 TranslateSpan TranslateSpan.SecpRawDeployment XlateSecpAlt.Topology
open XlateSecpAlt.Queries

theorem entry_look (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (c : XlateSecp.World.Card) (pcount : BitVec 88) :
    (fun a => (XlateSecpAlt.World.entry sem rho caller c pcount).mem[a]?) = fun a => XlateSecpAlt.World.plan.lookup a :=
  funext fun a => ReleaseProfile.GB10.SecpRuntime.StaticsAlt.mem_eq sem rho caller c pcount a

theorem shim_queries_of (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (c : XlateSecp.World.Card) (pcount : BitVec 88) (p : Plan) (start : Nat) (imm : BitVec 26) (closed : XlateSecp.Shim.ClosedAtShim p c start imm)
    {o : OracleChoice} :
    ∀ (checkedGlobal : CheckedTopology.check (XlateSecpAlt.Raw.Ro sem rho caller c pcount o)
        (DitShim243.Deployment.addresses p XlateSecp.World.base (XlateSecpAlt.World.entry sem rho caller c pcount) start imm
          (BitVec.ofNat 64 XlateSecp.Shim.shimPins.sp)) 4 = true),
      CheckedEntry.checkQueries (CheckedTopology.spec (XlateSecpAlt.Raw.Ro sem rho caller c pcount o) _ 4 checkedGlobal)
        (sourceAttributes rho caller) XlateSecp.World.permissionRows XlateSecp.World.mapping 1030
        (DitShim243.Deployment.selectedQueries p XlateSecp.World.base (XlateSecpAlt.World.entry sem rho caller c pcount) start imm
          (BitVec.ofNat 64 XlateSecp.Shim.shimPins.sp)) 4
        (ArmBridge.CruxGenGuarded.beforeFetchState (XlateSecpAlt.World.entry sem rho caller c pcount)) = true := by
  intro h
  rw [XlateSecp.Shim.shim_selected_eq, entry_gpr]
  exact closed rho caller (worldSpec_of_raw sem rho caller c pcount o _ h (XlateSecpAlt.World.payload c pcount).data)
    (XlateSecp.Queries.worldRegs_before (worldRegs_of_source sem rho caller c pcount)) _ (beforeFetch_regs _)

end XlateSecpAlt.Shim

#print axioms XlateSecpAlt.Shim.shim_queries_of
