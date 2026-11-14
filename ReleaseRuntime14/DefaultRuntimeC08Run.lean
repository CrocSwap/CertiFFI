-- Whole-run composition generated from signed runtime14 c08 rows.
import DefaultRuntimeC08Branch

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ArmCert.Translate.Model.StaticPie
open ArmCertValue CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option profiler true
set_option profiler.threshold 1000

namespace ReleaseProfile.DefaultRuntime
open PipeR14 PipeR14.Physical

def capacity_c08 : Nat := 0

def past_c08 : Nat → Nat
  | 0 => 0
  | _ => 0

def records_c08 {domain : QueryDomain} (spec : TopologyImageSpec domain) (p : R14E17.Pins) :
    Nat → List (Option ArmCertCTOrdered.OrderedEventV2.Record)
  | _ => []

#check "CURRENT_DECL steps_c08"
theorem steps_c08 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c08) (hpath : ArmCertPipe.PathOK (extend inputs D_c08) guards_c08)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c08.length ≤ budget) :
    ∀ k, k + 1 < plan_c08.length →
      StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c08 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c08 past_c08) (records_c08 spec p k) k := by
  intro k hk
  have len : plan_c08.length = 1 := rfl
  omega

#check "CURRENT_DECL run_c08"
theorem run_c08 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c08) (hpath : ArmCertPipe.PathOK (extend inputs D_c08) guards_c08)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c08.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c08 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c08 past_c08 0 entry) :
    (∀ k, k < plan_c08.length → ReleaseProfile.DefaultRuntime.Inv_c08 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c08 past_c08 k (stateAt real entry k)) ∧
    ∃ fin, modelStep real (stateAt real entry (plan_c08.length - 1)) = .ok () fin ∧
      ArmCertPipe.Physical.AgreesAt bytePA regions_c08 σ0_c08 inputs plan_c08 plan_c08.length fin ∧
      fin.regs._PC = base + BitVec.ofNat 64 0x2baa78 ∧ fin.regs._Z = entry.regs._Z ∧
      StepEvents.EvShape spec mapping (records_c08 spec p 0)
        (stateAt real entry (plan_c08.length - 1)) fin := by
  have len : plan_c08.length = 1 := rfl
  have chain := chain_of_evidence real entry 0 init (records_c08 spec p)
    (fun k hk => steps_c08 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath catalogue entry nodup hroom k (by omega))
  refine ⟨fun k hk => chain.1 k (by omega), ?_⟩
  obtain ⟨fin, run, agrees, pc, z, _dit, ev, _choice⟩ :=
    exit_c08 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c08 past_c08 nodup _ (chain.1 0 (by decide))
  exact ⟨fin, run, agrees, pc, z.trans (chain.2 0 (by decide)), ev⟩

#check "CURRENT_DECL dit_frame_c08"
/-- T6b DIT frame for c08: every state of the run, 0..1 (the state after the final step included), has the entry's
    PSTATE.DIT. Same premises as run_c08. -/
theorem dit_frame_c08 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c08) (hpath : ArmCertPipe.PathOK (extend inputs D_c08) guards_c08)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c08.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c08 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c08 past_c08 0 entry) :
    ∀ k, k ≤ plan_c08.length → (stateAt real entry k).regs.PSTATE.DIT = entry.regs.PSTATE.DIT := by
  have len : plan_c08.length = 1 := rfl
  have chain := chain_of_evidence real entry 0 init (records_c08 spec p)
    (fun k hk => steps_c08 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath catalogue entry nodup hroom k (by omega))
  have along := dit_of_evidence real entry 0 init (records_c08 spec p)
    (fun k hk => steps_c08 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath catalogue entry nodup hroom k (by omega))
  obtain ⟨fin, run, _, _, _, dit, _, _⟩ :=
    exit_c08 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c08 past_c08 nodup _ (chain.1 0 (by decide))
  intro k hk
  rcases Nat.lt_or_ge k 1 with h | h
  · exact along k (by omega)
  · have e : k = 0 + 1 := by omega
    rw [e, ArmCertValue.Physical.stateAt_succ_of' run]
    exact dit.trans (along 0 (by decide))

#print axioms steps_c08
#print axioms run_c08
#print axioms dit_frame_c08
end ReleaseProfile.DefaultRuntime
