import XlateSecp.Raw
import PipeLean_D234_SecpNeg_c10.EntryBinding

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# Secp topology check at the source-built entry (Translate, next train; speed mode)

`SecpRawDeployment.addresses` reads the entry only through its GPRs; the source-built entry's GPRs are the
world data's (`sourceRegs` keeps `data.gpr`). So the check reduces, without unfolding the register file, to
a closed `decide` over the world tables and the card's plan.
-/

namespace XlateSecp.Topology

open Sail ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ArmBridge.Draft
open ArmBridge.CruxGenGuarded NativeAccess ArmCertValue ArmCertPipe
open ReleaseProfile.MachineSource ReleaseProfile.GB10 TranslateSpan TranslateSpan.SecpRawDeployment

def gprAt (gpr : Vector (BitVec 64) 31) (pin : Nat) : BitVec 64 := if h : pin < 31 then gpr[pin] else 0

def regionVAG (gpr : Vector (BitVec 64) 31) (r : Region) (j : Nat) : BitVec 64 :=
  BitVec.addInt (gprAt gpr r.pin) (r.off + (j : Int))

def sitesG (p : Plan) (gpr : Vector (BitVec 64) 31) : List SelectedMap.Site :=
  p.accesses.map fun a => ⟨BitVec.addInt (gprAt gpr a.pin) a.offset, a.write⟩

def queriesG (p : Plan) (base : BitVec 64) (gpr : Vector (BitVec 64) 31) : List AccessQuery :=
  SelectedRepresentatives.queries (QueryDescriptors.data false) (QueryDescriptors.data true)
    QueryDescriptors.fetch (sitesG p gpr) (codeVAs p base) ++
  p.buffers.flatMap fun (r,n) => (List.range n).map fun j =>
    ⟨regionVAG gpr r j, ⟨QueryDescriptors.data (p.outputs.any (fun (g,_) => g == r)), true⟩, 1⟩

def addressesG (p : Plan) (base : BitVec 64) (gpr : Vector (BitVec 64) 31) : List (BitVec 64) :=
  (queriesG p base gpr).map (·.va)

theorem addresses_eq (p : Plan) (base : BitVec 64) (e : ArmBridge.Draft.NativeState) :
    addresses p base e = addressesG p base e.regs.gpr := rfl

theorem entry_gpr (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (c : World.Card) (pcount : BitVec 88) : (World.entry sem rho caller c pcount).regs.gpr = (World.data c).gpr := rfl

end XlateSecp.Topology

