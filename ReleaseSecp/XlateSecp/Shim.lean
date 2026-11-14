import XlateSecp.Queries
import XlateSecp.LayoutAll
import SecpStatics
import DitShim243.Deployment
import DitShim243.SlotCheck

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# Secp shim-entry (scope B) generic leaves (Translate; speed mode)

The shim-extended plan (`DitShim243.Deployment.extend p start imm`) and its global address list read the entry only
through its GPRs and the constant save slot; restated over the GPR vector (`rfl`) so per-card checks are closed
decisions. The queries (route B) reuse `XlateSecp.Queries` (WorldSpec/WorldRegs + `a124_tac`).
-/

namespace XlateSecp.Shim

open Sail ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ArmBridge.Draft
open ArmBridge.CruxGenGuarded NativeAccess ArmCertValue ArmCertPipe
open ReleaseProfile.MachineSource ReleaseProfile.GB10 TranslateSpan TranslateSpan.SecpRawDeployment XlateSecp.Topology
open XlateSecp.Queries

/-- Shim save slot / pins: SP_EL0 = 0x50000 at entry, the 16-byte frame at 0x4fff0 (stack page 0x4f, zeroed). -/
def shimPins : HeapV2E17.Pins := ⟨0x4fff0, 0x30000, 0x31000⟩

def bufferQueriesG (p : Plan) (gpr : Vector (BitVec 64) 31) : List AccessQuery :=
  p.buffers.flatMap fun (r,n) => (List.range n).map fun j =>
    ⟨regionVAG gpr r j, ⟨QueryDescriptors.data (p.outputs.any (fun (g,_) => g == r)), true⟩, 1⟩

def queriesShimG (p : Plan) (base : BitVec 64) (gpr : Vector (BitVec 64) 31) (start : Nat) (imm : BitVec 26)
    (slot : BitVec 64) : List AccessQuery :=
  SelectedRepresentatives.queries (QueryDescriptors.data false) (QueryDescriptors.data true)
    QueryDescriptors.fetch (sitesG p gpr ++ [⟨slot,false⟩,⟨slot,true⟩]) (codeVAs (DitShim243.Deployment.extend p start imm) base) ++
  bufferQueriesG p gpr

def selectedShimG (p : Plan) (base : BitVec 64) (gpr : Vector (BitVec 64) 31) (start : Nat) (imm : BitVec 26)
    (slot : BitVec 64) : List AccessQuery :=
  SelectedRepresentatives.queries (QueryDescriptors.data false) (QueryDescriptors.data true)
    QueryDescriptors.fetch (sitesG p gpr ++ [⟨slot,false⟩,⟨slot,true⟩]) (codeVAs (DitShim243.Deployment.extend p start imm) base)

theorem shim_selected_eq (p : Plan) (base : BitVec 64) (e : NativeState) (start : Nat) (imm : BitVec 26) (slot : BitVec 64) :
    DitShim243.Deployment.selectedQueries p base e start imm slot = selectedShimG p base e.regs.gpr start imm slot := rfl

theorem shim_queries_eq (p : Plan) (base : BitVec 64) (e : NativeState) (start : Nat) (imm : BitVec 26) (slot : BitVec 64) :
    DitShim243.Deployment.queries p base e start imm slot = queriesShimG p base e.regs.gpr start imm slot := rfl

theorem shim_addresses_eq (p : Plan) (base : BitVec 64) (e : NativeState) (start : Nat) (imm : BitVec 26) (slot : BitVec 64) :
    DitShim243.Deployment.addresses p base e start imm slot = (queriesShimG p base e.regs.gpr start imm slot).map (·.va) := rfl

theorem view_eq (p : Plan) (mapping : BitVec 64 → Option Nat) (e : NativeState) :
    view p mapping e = LayoutAll.viewG p mapping e.regs.gpr := rfl

/-- Slot check with the entry memory as a lookup function. -/
def slotCheckL (pins : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (fp : Footprint)
    (look : Nat → Option (BitVec 8)) : Bool :=
  let va := BitVec.ofNat 64 pins.sp
  match mapping va with
  | none => false
  | some n => SelectedLoadFacts.checkRAM mapping va && (decide (n + 16 < 2 ^ 56) &&
      ((List.range 16).all (fun i => !(StaticLayout.footprintByte fp (n + i)) && (look (n + i)).isSome) &&
      (decide (mapping (plus8 va) = some (n+8)) && SelectedLoadFacts.checkRAM mapping (plus8 va))))

theorem slot_eq (pins : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (fp : Footprint) (e : NativeState) :
    DitShim243.SlotCheck.check pins mapping fp e = slotCheckL pins mapping fp (fun a => e.mem[a]?) := rfl

theorem entry_look (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (c : World.Card) (pcount : BitVec 88) :
    (fun a => (World.entry sem rho caller c pcount).mem[a]?) = fun a => World.plan.lookup a :=
  funext fun a => ReleaseProfile.GB10.SecpRuntime.Statics.mem_eq sem rho caller c pcount a

/-- Closed per-card global (shim-extended) query check. -/
def ClosedAtShim (p : Plan) (c : World.Card) (start : Nat) (imm : BitVec 26) : Prop :=
  ∀ (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) {domain : QueryDomain}
    {spec : TopologyImageSpec domain}, WorldSpec spec → ∀ {R : Regs} {tcr sctlr : BitVec 64}, WorldRegs R tcr sctlr →
    ∀ e : ArmCertWalk.State, e.regs = R →
    CheckedEntry.checkQueries spec (sourceAttributes rho caller) World.permissionRows World.mapping 1030
      (selectedShimG p World.base (World.data c).gpr start imm (BitVec.ofNat 64 shimPins.sp)) 4 e = true

theorem shim_queries_of (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (c : World.Card) (pcount : BitVec 88) (p : Plan) (start : Nat) (imm : BitVec 26) (closed : ClosedAtShim p c start imm)
    {o : OracleChoice} :
    ∀ (checkedGlobal : CheckedTopology.check (Raw.Ro sem rho caller c pcount o)
        (DitShim243.Deployment.addresses p World.base (World.entry sem rho caller c pcount) start imm
          (BitVec.ofNat 64 shimPins.sp)) 4 = true),
      CheckedEntry.checkQueries (CheckedTopology.spec (Raw.Ro sem rho caller c pcount o) _ 4 checkedGlobal)
        (sourceAttributes rho caller) World.permissionRows World.mapping 1030
        (DitShim243.Deployment.selectedQueries p World.base (World.entry sem rho caller c pcount) start imm
          (BitVec.ofNat 64 shimPins.sp)) 4
        (ArmBridge.CruxGenGuarded.beforeFetchState (World.entry sem rho caller c pcount)) = true := by
  intro h
  rw [shim_selected_eq, entry_gpr]
  exact closed rho caller (worldSpec_of_raw sem rho caller c pcount o _ h (World.payload c pcount).data)
    (worldRegs_before (worldRegs_of_source sem rho caller c pcount)) _ (beforeFetch_regs _)

end XlateSecp.Shim

#print axioms XlateSecp.Shim.shim_queries_of
