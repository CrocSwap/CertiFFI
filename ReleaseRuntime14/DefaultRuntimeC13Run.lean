-- Whole-run composition generated from signed runtime14 c13 rows.
import DefaultRuntimeC13Mem
import DefaultRuntimeC13Class
import DefaultRuntimeC13Branch

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

def capacity_c13 : Nat := 1

def past_c13 : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | _ => 1

def records_c13 {domain : QueryDomain} (spec : TopologyImageSpec domain) (p : R14E17.Pins) :
    Nat → List (Option ArmCertCTOrdered.OrderedEventV2.Record)
  | 1 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 19 (0))) false 4
  | _ => []

#check "CURRENT_DECL steps_c13"
theorem steps_c13 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c13) (hpath : ArmCertPipe.PathOK (extend inputs D_c13) guards_c13)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c13 regions_c13 sc base) (hp : PinsAgree p rs_c13 forms_c13 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c13.length ≤ budget) :
    ∀ k, k + 1 < plan_c13.length →
      StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c13 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c13 past_c13) (records_c13 spec p k) k := by
  intro k hk
  have len : plan_c13.length = 5 := rfl
  match k, hk with
  | 0, hk => exact step_c13_0 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c13 past_c13 (by decide) nodup
  | 1, hk => exact step_c13_1 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c13 past_c13 (by decide) (by decide) nodup
  | 2, hk => exact step_c13_2 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c13 past_c13 (by decide) nodup
  | 3, hk => exact step_c13_3 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c13 past_c13 (by decide) nodup
  | j + 4, hk => exact False.elim (by omega)

#check "CURRENT_DECL run_c13"
theorem run_c13 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c13) (hpath : ArmCertPipe.PathOK (extend inputs D_c13) guards_c13)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c13 regions_c13 sc base) (hp : PinsAgree p rs_c13 forms_c13 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c13.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c13 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c13 past_c13 0 entry) :
    (∀ k, k < plan_c13.length → ReleaseProfile.DefaultRuntime.Inv_c13 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c13 past_c13 k (stateAt real entry k)) ∧
    ∃ fin, modelStep real (stateAt real entry (plan_c13.length - 1)) = .ok () fin ∧
      ArmCertPipe.Physical.AgreesAt bytePA regions_c13 σ0_c13 inputs plan_c13 plan_c13.length fin ∧
      fin.regs._PC = base + BitVec.ofNat 64 0x2b6b2c ∧ fin.regs._Z = entry.regs._Z ∧
      StepEvents.EvShape spec mapping (records_c13 spec p 4)
        (stateAt real entry (plan_c13.length - 1)) fin := by
  have len : plan_c13.length = 5 := rfl
  have chain := chain_of_evidence real entry 4 init (records_c13 spec p)
    (fun k hk => steps_c13 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath ds hp catalogue entry nodup hroom k (by omega))
  refine ⟨fun k hk => chain.1 k (by omega), ?_⟩
  obtain ⟨fin, run, agrees, pc, z, _dit, ev, _choice⟩ :=
    exit_c13 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c13 past_c13 nodup _ (chain.1 4 (by decide))
  exact ⟨fin, run, agrees, pc, z.trans (chain.2 4 (by decide)), ev⟩

#check "CURRENT_DECL dit_frame_c13"
/-- T6b DIT frame for c13: every state of the run, 0..5 (the state after the final step included), has the entry's
    PSTATE.DIT. Same premises as run_c13. -/
theorem dit_frame_c13 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c13) (hpath : ArmCertPipe.PathOK (extend inputs D_c13) guards_c13)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c13 regions_c13 sc base) (hp : PinsAgree p rs_c13 forms_c13 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c13.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c13 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c13 past_c13 0 entry) :
    ∀ k, k ≤ plan_c13.length → (stateAt real entry k).regs.PSTATE.DIT = entry.regs.PSTATE.DIT := by
  have len : plan_c13.length = 5 := rfl
  have chain := chain_of_evidence real entry 4 init (records_c13 spec p)
    (fun k hk => steps_c13 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath ds hp catalogue entry nodup hroom k (by omega))
  have along := dit_of_evidence real entry 4 init (records_c13 spec p)
    (fun k hk => steps_c13 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath ds hp catalogue entry nodup hroom k (by omega))
  obtain ⟨fin, run, _, _, _, dit, _, _⟩ :=
    exit_c13 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c13 past_c13 nodup _ (chain.1 4 (by decide))
  intro k hk
  rcases Nat.lt_or_ge k 5 with h | h
  · exact along k (by omega)
  · have e : k = 4 + 1 := by omega
    rw [e, ArmCertValue.Physical.stateAt_succ_of' run]
    exact dit.trans (along 4 (by decide))

#print axioms steps_c13
#print axioms run_c13
#print axioms dit_frame_c13
end ReleaseProfile.DefaultRuntime
