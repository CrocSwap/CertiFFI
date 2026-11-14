-- Whole-run composition generated from signed runtime14 c09 rows.
import DefaultRuntimeC09Mem
import DefaultRuntimeC09Class
import DefaultRuntimeC09Branch

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

def capacity_c09 : Nat := 2

def past_c09 : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | _ => 2

def records_c09 {domain : QueryDomain} (spec : TopologyImageSpec domain) (p : R14E17.Pins) :
    Nat → List (Option ArmCertCTOrdered.OrderedEventV2.Record)
  | 1 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 0 (0))) false 4
  | 5 => HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 0 (0))) true 4
  | _ => []

#check "CURRENT_DECL steps_c09"
theorem steps_c09 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c09) (hpath : ArmCertPipe.PathOK (extend inputs D_c09) guards_c09)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c09 regions_c09 sc base) (hp : PinsAgree p rs_c09 forms_c09 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c09.length ≤ budget) :
    ∀ k, k + 1 < plan_c09.length →
      StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c09 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c09 past_c09) (records_c09 spec p k) k := by
  intro k hk
  have len : plan_c09.length = 6 := rfl
  match k, hk with
  | 0, hk => exact step_c09_0 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c09 past_c09 (by decide) nodup
  | 1, hk => exact step_c09_1 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c09 past_c09 (by decide) (by decide) nodup
  | 2, hk => exact step_c09_2 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c09 past_c09 (by decide) nodup
  | 3, hk => exact step_c09_3 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page low hlen hpath catalogue entry capacity_c09 past_c09 (by decide) nodup
  | 4, hk => exact step_c09_4 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen catalogue entry capacity_c09 past_c09 (by decide) nodup
  | j + 5, hk => exact False.elim (by omega)

#check "CURRENT_DECL run_c09"
theorem run_c09 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c09) (hpath : ArmCertPipe.PathOK (extend inputs D_c09) guards_c09)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c09 regions_c09 sc base) (hp : PinsAgree p rs_c09 forms_c09 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c09.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c09 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c09 past_c09 0 entry) :
    (∀ k, k < plan_c09.length → ReleaseProfile.DefaultRuntime.Inv_c09 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c09 past_c09 k (stateAt real entry k)) ∧
    ∃ fin, modelStep real (stateAt real entry (plan_c09.length - 1)) = .ok () fin ∧
      ArmCertPipe.Physical.AgreesAt bytePA regions_c09 σ0_c09 inputs plan_c09 plan_c09.length fin ∧
      fin.regs._PC = base + (offset_c09 5 + 4#64) ∧ fin.regs._Z = entry.regs._Z ∧
      StepEvents.EvShape spec mapping (records_c09 spec p 5)
        (stateAt real entry (plan_c09.length - 1)) fin := by
  have len : plan_c09.length = 6 := rfl
  have chain := chain_of_evidence real entry 5 init (records_c09 spec p)
    (fun k hk => steps_c09 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath ds hp catalogue entry nodup hroom k (by omega))
  refine ⟨fun k hk => chain.1 k (by omega), ?_⟩
  obtain ⟨fin, run, agrees, pc, z, _dit, ev, _choice⟩ :=
    exit_c09 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c09 past_c09 (by decide) nodup _ (chain.1 5 (by decide))
  exact ⟨fin, run, agrees, pc, z.trans (chain.2 5 (by decide)), ev⟩

#check "CURRENT_DECL dit_frame_c09"
/-- T6b DIT frame for c09: every state of the run, 0..6 (the state after the final step included), has the entry's
    PSTATE.DIT. Same premises as run_c09. -/
theorem dit_frame_c09 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c09) (hpath : ArmCertPipe.PathOK (extend inputs D_c09) guards_c09)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c09 regions_c09 sc base) (hp : PinsAgree p rs_c09 forms_c09 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c09.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c09 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c09 past_c09 0 entry) :
    ∀ k, k ≤ plan_c09.length → (stateAt real entry k).regs.PSTATE.DIT = entry.regs.PSTATE.DIT := by
  have len : plan_c09.length = 6 := rfl
  have chain := chain_of_evidence real entry 5 init (records_c09 spec p)
    (fun k hk => steps_c09 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath ds hp catalogue entry nodup hroom k (by omega))
  have along := dit_of_evidence real entry 5 init (records_c09 spec p)
    (fun k hk => steps_c09 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath ds hp catalogue entry nodup hroom k (by omega))
  obtain ⟨fin, run, _, _, _, dit, _, _⟩ :=
    exit_c09 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs (by omega) page hlen ds hp catalogue entry capacity_c09 past_c09 (by decide) nodup _ (chain.1 5 (by decide))
  intro k hk
  rcases Nat.lt_or_ge k 6 with h | h
  · exact along k (by omega)
  · have e : k = 5 + 1 := by omega
    rw [e, ArmCertValue.Physical.stateAt_succ_of' run]
    exact dit.trans (along 5 (by decide))

#print axioms steps_c09
#print axioms run_c09
#print axioms dit_frame_c09
end ReleaseProfile.DefaultRuntime
